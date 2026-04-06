#!/usr/bin/env ruby
# frozen_string_literal: true

require "optparse"
require "cgi"
require "set"
require "uri"
require "epub/parser"
require "nokogiri"

module EpubStructuredText
  Event = Struct.new(:type, :level, :depth, :text, keyword_init: true)
  NavSection = Struct.new(:key, :text, :depth, :item, :fragment, :children, :parent, keyword_init: true)
  Marker = Struct.new(:section, :start_node, :position, :heading_text, :lineage, keyword_init: true)
  LossRecord = Struct.new(:category, :message, :context, :payload, keyword_init: true)

  class CLI
    def self.run(argv)
      new.run(argv)
    end

    def run(argv)
      options = {
        output: nil,
        include_metadata: true
      }

      parser = OptionParser.new do |opt|
        opt.banner = <<~BANNER
          Convert an EPUB into a structured plain-text representation.

          Usage: #{File.basename($PROGRAM_NAME)} [options] INPUT.epub
        BANNER

        opt.on("-o", "--output=FILE", "Write output to FILE instead of stdout") do |path|
          options[:output] = path
        end

        opt.on("--no-metadata", "Do not emit the metadata header") do
          options[:include_metadata] = false
        end

        opt.on("-h", "--help", "Show this help") do
          puts opt
          exit 0
        end
      end

      parser.parse!(argv)
      input = argv.shift
      raise ArgumentError, "missing INPUT.epub" if input.nil? || input.strip.empty?

      book = parse_book(input)
      text = Extractor.new(book, options).call

      if options[:output]
        File.write(options[:output], text)
      else
        puts text
      end
    rescue StandardError => e
      warn "error: #{e.message}"
      exit 1
    end

    private

    def parse_book(input)
      EPUB::Parser.parse(input, container_adapter: adapter_for(input))
    end

    def adapter_for(input)
      return :UnpackedDirectory if File.directory?(input)
      return nil if File.file?(input)

      uri = URI.parse(input)
      return :UnpackedURI if uri.scheme && !uri.scheme.empty?

      raise ArgumentError, "input is neither a readable file, a directory, nor a URI"
    rescue URI::InvalidURIError
      raise ArgumentError, "input is neither a readable file, a directory, nor a URI"
    end
  end

  class Extractor
    EPUB_NS = "http://www.idpf.org/2007/ops"
    NOISE_PATTERN = /(?:^|[\s_-])(page(?:num|number)?|pagenum|folio|running[\s_-]?head|running[\s_-]?header|header|footer)(?:$|[\s_-])/i
    NOTE_PATTERN = /(?:^|[\s_-])(note|notes|footnote|footnotes|endnote|endnotes|rearnote|rearnotes|annotation|annotations)(?:$|[\s_-])/i
    NOTE_REF_PATTERN = /(?:^|[\s_-])(noteref|doc-noteref|footnote-ref|endnote-ref)(?:$|[\s_-])/i
    HIDDEN_DECLARATION_PATTERN = /(?:display\s*:\s*none|visibility\s*:\s*hidden|content-visibility\s*:\s*hidden)/i
    HEADING_XPATH = ".//*[self::*[local-name()='h1'] or self::*[local-name()='h2'] or self::*[local-name()='h3'] or self::*[local-name()='h4'] or self::*[local-name()='h5'] or self::*[local-name()='h6']]"

    def initialize(book, options)
      @book = book
      @options = options
      @doc_cache = {}
      @body_cache = {}
      @heading_nodes_cache = {}
      @position_cache = {}
      @subtree_end_cache = {}
      @range_cache = {}
      @hidden_selectors_cache = {}
      @losses = []
    end

    def call
      parts = []
      parts << render_metadata if @options[:include_metadata]
      parts << render_hybrid_body
      parts << render_loss_report
      normalize_output(parts.reject(&:empty?).join("\n\n"))
    end

    private

    def render_metadata
      lines = []
      lines << "Title: #{safe_scalar(@book.title)}"

      creators = Array(@book.metadata&.creators).map(&:to_s).map(&:strip).reject(&:empty?)
      lines << "Creators: #{creators.join('; ')}" unless creators.empty?

      languages = Array(@book.metadata&.languages).map(&:to_s).map(&:strip).reject(&:empty?)
      lines << "Languages: #{languages.join(', ')}" unless languages.empty?

      modified = @book.modified
      lines << "Modified: #{safe_scalar(modified)}" unless modified.nil? || modified.to_s.strip.empty?
      lines.join("\n")
    end

    def render_hybrid_body
      root_sections = usable_root_sections
      lines = []

      @book.each_page_on_spine.each do |item|
        unless item.xhtml?
          record_loss(
            "skipped_spine_item",
            "Skipped non-XHTML spine item.",
            context: item_context(item)
          )
          next
        end

        if item.nav?
          record_loss(
            "skipped_spine_item",
            "Skipped navigation document on spine.",
            context: item_context(item)
          )
          next
        end

        body = body_for(item)
        next unless body

        if root_sections
          markers = build_markers_for_item(root_sections, item)
          if markers.empty?
            record_loss(
              "orphan_spine_item",
              "Rendered spine item without TOC markers.",
              context: item_context(item)
            )
            render_orphan_item(item, lines)
          else
            render_item_with_markers(item, markers, lines)
          end
        else
          record_loss(
            "orphan_spine_item",
            "Rendered spine item without a usable TOC.",
            context: item_context(item)
          )
          render_orphan_item(item, lines)
        end
      end

      lines.join("\n")
    end

    def usable_root_sections
      toc = safe_toc
      return nil unless toc

      sections = build_sections(Array(toc.items))
      if sections.empty?
        record_loss(
          "empty_toc",
          "Navigation TOC was present but yielded no usable sections.",
          context: {}
        )
        nil
      else
        sections
      end
    end

    def safe_toc
      @book.nav&.content_document&.toc
    rescue StandardError => e
      record_loss(
        "toc_unavailable",
        "Failed to read navigation TOC; falling back to orphan rendering.",
        context: { error_class: e.class.name },
        payload: e.message
      )
      nil
    end

    def build_sections(items, depth = 0, parent = nil)
      items.each_with_index.filter_map do |nav_item, index|
        text = normalize_space(nav_item.text.to_s)
        href = nav_item.href
        section_item = href ? nav_item.item : nil
        fragment = href&.fragment
        key = [depth, index, section_item&.id, fragment, text, parent&.key].join("\u0000")

        section = NavSection.new(
          key: key,
          text: text,
          depth: depth,
          item: section_item,
          fragment: fragment,
          children: [],
          parent: parent
        )

        section.children = build_sections(Array(nav_item.items), depth + 1, section)
        next if text.empty? && section.item.nil? && section.children.empty?

        section
      end
    rescue StandardError => e
      record_loss(
        "toc_build_failure",
        "Failed while building TOC sections.",
        context: {
          depth: depth,
          parent_key: parent&.key,
          error_class: e.class.name
        },
        payload: e.message
      )
      []
    end

    def collect_item_sections(sections, item_id, out = [])
      sections.each do |section|
        out << section if section.item&.id == item_id
        collect_item_sections(section.children, item_id, out)
      end
      out
    end

    def build_markers_for_item(root_sections, item)
      item_sections = collect_item_sections(root_sections, item.id)
      return [] if item_sections.empty?

      resolved = item_sections.filter_map do |section|
        start_node = resolve_start_node(section)
        unless start_node
          record_loss(
            "unresolved_toc_entry",
            "Could not resolve TOC entry to a concrete start node.",
            context: section_context(section)
          )
          next
        end

        position = node_position(item, start_node)
        unless position.finite?
          record_loss(
            "unpositioned_toc_entry",
            "Resolved TOC node could not be positioned in document order.",
            context: section_context(section).merge(path: safe_scalar(start_node.path))
          )
          next
        end

        heading_text = section_heading(section)
        lineage = lineage_for(section)

        Marker.new(
          section: section,
          start_node: start_node,
          position: position,
          heading_text: heading_text,
          lineage: lineage
        )
      end

      return [] if resolved.empty?

      sorted = resolved.sort_by { |marker| [marker.position, marker.section.depth, marker.section.key] }
      dedupe_markers(sorted)
    end

    def dedupe_markers(markers)
      deduped = []
      last_position = nil
      last_key = nil

      markers.each do |marker|
        position = marker.position
        key = [position, normalize_space(marker.heading_text.to_s), marker.section.depth]

        if !last_position.nil? && position == last_position
          if key == last_key
            record_loss(
              "duplicate_marker_removed",
              "Removed duplicate TOC marker at the same document position.",
              context: section_context(marker.section)
            )
            next
          end

          if more_specific_lineage?(marker, deduped.last)
            displaced = deduped.last
            deduped[-1] = marker
            last_key = key
            record_loss(
              "marker_replaced",
              "Replaced a same-position marker with one that has a more specific lineage.",
              context: {
                replaced_section: displaced&.section&.text,
                replacement_section: marker.section.text,
                position: position
              }
            )
          else
            record_loss(
              "marker_discarded",
              "Discarded a same-position marker because an existing marker had equal or greater specificity.",
              context: {
                discarded_section: marker.section.text,
                retained_section: deduped.last&.section&.text,
                position: position
              }
            )
          end
          next
        end

        deduped << marker
        last_position = position
        last_key = key
      end

      deduped
    end

    def more_specific_lineage?(candidate, current)
      return true if current.nil?

      candidate.lineage.length > current.lineage.length
    end

    def resolve_start_node(section)
      unless section.item&.xhtml?
        record_loss(
          "section_item_not_xhtml",
          "TOC entry points at a non-XHTML resource.",
          context: section_context(section)
        )
        return nil
      end

      body = body_for(section.item)
      unless body
        record_loss(
          "section_body_missing",
          "TOC entry points at a resource whose body could not be parsed.",
          context: section_context(section)
        )
        return nil
      end

      if !section.fragment.to_s.empty?
        anchor = find_fragment_node(section.item, section.fragment)
        if anchor
          node = nearest_block_or_heading(anchor, body) || anchor
          return node if node_position(section.item, node).finite?

          record_loss(
            "toc_fragment_unpositioned",
            "TOC fragment resolved, but its enclosing start node could not be positioned.",
            context: section_context(section).merge(path: safe_scalar(node.path))
          )
        else
          record_loss(
            "toc_fragment_missing",
            "TOC fragment did not resolve to an element id/xml:id.",
            context: section_context(section)
          )
        end
      end

      heading = find_heading_node(section.item, section.text)
      return heading if heading

      nil
    end

    def find_fragment_node(item, fragment)
      doc = document_for(item)
      return nil unless doc

      xpath = "//*[@id=#{xpath_string(fragment)} or @xml:id=#{xpath_string(fragment)}]"
      doc.at_xpath(xpath)
    rescue StandardError => e
      record_loss(
        "fragment_lookup_error",
        "Failed while resolving a TOC fragment.",
        context: item_context(item).merge(fragment: fragment, error_class: e.class.name),
        payload: e.message
      )
      nil
    end

    def find_heading_node(item, text)
      target = normalize_space(text.to_s)
      return nil if target.empty?

      headings = heading_nodes_for(item)
      return nil if headings.empty?

      exact = headings.find { |node| normalize_space(node.text.to_s) == target }
      return exact if exact

      normalized_target = canonical_heading_key(target)

      headings.find do |node|
        candidate = normalize_space(node.text.to_s)
        next false if candidate.empty?

        canonical_heading_key(candidate) == normalized_target
      end
    end

    def canonical_heading_key(text)
      normalize_space(text).downcase.gsub(/[^\p{Alnum}\s]/u, " ").gsub(/[[:space:]]+/, " ").strip
    end

    def heading_nodes_for(item)
      @heading_nodes_cache[item.id] ||= begin
        body = body_for(item)
        body ? body.xpath(HEADING_XPATH).to_a : []
      end
    end

    def lineage_for(section)
      nodes = []
      current = section

      while current
        text =
          if current.equal?(section)
            section_heading(current)
          else
            normalize_space(current.text.to_s)
          end

        unless text.empty?
          nodes << {
            key: current.key,
            level: [[current.depth + 1, 1].max, 6].min,
            text: text
          }
        end

        current = current.parent
      end

      nodes.reverse
    end

    def render_item_with_markers(item, markers, lines)
      body = body_for(item)
      return unless body

      emitted_stack = []
      cursor = body

      markers.each_with_index do |marker, index|
        next_start = index + 1 < markers.length ? markers[index + 1].start_node : nil

        render_gap(item, cursor, marker.start_node, lines, base_heading_level: 1)
        emit_lineage(marker.lineage, emitted_stack, lines)
        render_range(
          item,
          marker.start_node,
          next_start,
          lines,
          heading_text: marker.heading_text,
          heading_offset: marker.section.depth
        )

        cursor = next_start
      end

      render_gap(item, cursor, nil, lines, base_heading_level: 1) if cursor
    end

    def emit_lineage(lineage, emitted_stack, lines)
      shared = 0

      while shared < lineage.length && shared < emitted_stack.length
        current = lineage[shared]
        prior = emitted_stack[shared]
        break unless current[:key] == prior[:key] && current[:text] == prior[:text] && current[:level] == prior[:level]

        shared += 1
      end

      emitted_stack.slice!(shared, emitted_stack.length - shared)

      lineage[shared..].to_a.each do |entry|
        lines << "" unless lines.empty? || lines.last.empty?
        lines << ("#" * entry[:level]) + " " + entry[:text]
        lines << ""
        emitted_stack << entry
      end
    end

    def render_orphan_item(item, lines)
      body = body_for(item)
      return unless body

      events = HTMLWalker.new(body).events
      normalize_heading_levels!(events)

      if events.none? { |event| event.type == :heading }
        heading = fallback_heading(item, document_for(item))
        unless heading.empty?
          events.unshift(Event.new(type: :heading, level: 1, text: heading))
          record_loss(
            "fallback_heading_inserted",
            "Inserted fallback heading because no heading was found in orphan-rendered content.",
            context: item_context(item).merge(heading: heading)
          )
        end
      end

      render_events(events, lines, heading_offset: 0) unless events.empty?
    end

    def render_gap(item, start_node, end_node, lines, base_heading_level:)
      return if start_node == end_node
      return if start_node.nil? && end_node.nil?

      body = body_for(item)
      actual_start = start_node || body
      return unless actual_start

      events = range_events(item, actual_start, end_node)
      return if events.empty?

      if events.none? { |event| event.type == :heading } && gap_needs_fallback_heading?(item, actual_start)
        heading = fallback_heading(item, document_for(item))
        unless heading.empty?
          events.unshift(Event.new(type: :heading, level: 1, text: heading))
          record_loss(
            "fallback_heading_inserted",
            "Inserted fallback heading for pre-marker gap content.",
            context: item_context(item).merge(heading: heading)
          )
        end
      end

      render_events(events, lines, heading_offset: [base_heading_level - 1, 0].max)
    end

    def render_range(item, start_node, end_node, lines, heading_text:, heading_offset:)
      return if start_node == end_node

      events = range_events(item, start_node, end_node)
      return if events.empty?

      if heading_text && events.first&.type == :heading && normalize_space(events.first.text) == normalize_space(heading_text)
        events = events.drop(1)
      end

      render_events(events, lines, heading_offset: heading_offset) unless events.empty?
    end

    def range_events(item, start_node, end_node)
      body = body_for(item)
      return [] unless body

      start_position = node_position(item, start_node)
      stop_position = node_position(item, end_node)
      normalized_start = start_position.finite? ? start_position : 0
      normalized_stop = stop_position.finite? ? stop_position : nil

      cache_key = [item.id, normalized_start, normalized_stop]

      @range_cache[cache_key] ||= begin
        walker = HTMLWalker.new(
          body,
          include_root: false,
          start_position: normalized_start,
          stop_position: normalized_stop,
          position_lookup: ->(node) { node_position(item, node) },
          subtree_end_lookup: ->(node) { subtree_end_position(item, node) }
        )
        events = walker.events
        normalize_heading_levels!(events)
        events
      end
    end

    def render_events(events, lines, heading_offset:)
      events.each do |event|
        case event.type
        when :heading
          level = [[event.level.to_i + heading_offset, 1].max, 6].min
          lines << "" unless lines.empty? || lines.last.empty?
          lines << ("#" * level) + " " + event.text
          lines << ""
        when :paragraph
          lines << event.text
          lines << ""
        when :list_item
          indent = "  " * [event.depth - 1, 0].max
          lines << "#{indent}- #{event.text}"
        when :blockquote
          event.text.split("\n").each { |line| lines << "> #{line}" }
          lines << ""
        when :preformatted
          lines << "```"
          lines.concat(event.text.split("\n"))
          lines << "```"
          lines << ""
        end
      end
    end

    def gap_needs_fallback_heading?(item, start_node)
      body = body_for(item)
      return false unless body

      start_node == body
    end

    def section_heading(section)
      text = normalize_space(section.text.to_s)
      return text unless text.empty?
      return "" unless section.item

      fallback_heading(section.item, document_for(section.item))
    end

    def document_for(item)
      @doc_cache[item.id] ||= parse_xhtml(item)
    end

    def body_for(item)
      @body_cache[item.id] ||= begin
        doc = document_for(item)
        if doc.nil?
          nil
        else
          body = doc.at_xpath("//*[local-name()='body']")
          if body.nil?
            record_loss(
              "xhtml_without_body",
              "Parsed XHTML resource has no <body> element.",
              context: item_context(item),
              payload: safe_payload(doc.to_xml)
            )
            nil
          else
            apply_hidden_css_rules!(item, doc, body)
            clean_noise!(item, body)
            build_position_cache(item, body)
            body
          end
        end
      end
    end

    def parse_xhtml(item)
      content = item.read(detect_encoding: true)
      doc = Nokogiri::XML(content)

      Array(doc.errors).each do |error|
        record_loss(
          "xml_parse_issue",
          "Nokogiri reported a parse issue while loading this XHTML resource.",
          context: item_context(item).merge(
            line: error.respond_to?(:line) ? error.line : nil,
            column: error.respond_to?(:column) ? error.column : nil,
            level: error.respond_to?(:level) ? error.level : nil
          ),
          payload: error.to_s
        )
      end

      if doc.root.nil?
        record_loss(
          "xhtml_without_root",
          "Parsed XHTML resource has no root element.",
          context: item_context(item),
          payload: safe_payload(content)
        )
        return nil
      end

      doc
    rescue StandardError => e
      record_loss(
        "xhtml_parse_failure",
        "Failed to parse XHTML resource.",
        context: item_context(item).merge(error_class: e.class.name),
        payload: e.message
      )
      nil
    end

    def apply_hidden_css_rules!(item, doc, body)
      hidden_selectors_for(doc).each do |selector|
        begin
          doc.css(selector).each do |node|
            next unless node.element?
            next unless node == body || node.ancestors.include?(body)

            record_loss(
              "hidden_css_removed_node",
              "Removed node because a document stylesheet hides it.",
              context: item_context(item).merge(
                selector: selector,
                path: safe_scalar(node.path),
                tag: node.name
              ),
              payload: safe_markup(node)
            )
            node.remove
          end
        rescue Nokogiri::CSS::SyntaxError => e
          record_loss(
            "hidden_css_selector_invalid",
            "Could not evaluate a CSS selector extracted from inline styles.",
            context: item_context(item).merge(selector: selector, error_class: e.class.name),
            payload: e.message
          )
        end
      end
    end

    def hidden_selectors_for(doc)
      @hidden_selectors_cache[doc.object_id] ||= begin
        css_text = doc.xpath("//*[local-name()='style']").map(&:text).join("\n")
        selectors = []

        css_text.scan(/([^{}]+)\{([^{}]+)\}/m) do |raw_selectors, declarations|
          next unless declarations.match?(HIDDEN_DECLARATION_PATTERN)
          next if raw_selectors.include?("@")

          raw_selectors.split(",").each do |selector|
            cleaned = selector.strip
            next if cleaned.empty?
            next if cleaned.include?("::")

            selectors << cleaned
          end
        end

        selectors.uniq
      end
    end

    def build_position_cache(item, body)
      return if @position_cache[item.id]

      positions = {}
      subtree_ends = {}
      assign_positions(body, positions, subtree_ends, 0)

      @position_cache[item.id] = positions
      @subtree_end_cache[item.id] = subtree_ends
    end

    def assign_positions(node, positions, subtree_ends, next_index)
      positions[node.object_id] = next_index
      current = next_index + 1

      node.children.each do |child|
        current = assign_positions(child, positions, subtree_ends, current)
      end

      subtree_ends[node.object_id] = current - 1
      current
    end

    def node_position(item, node)
      return Float::INFINITY if node.nil?

      body_for(item)
      @position_cache.fetch(item.id, {}).fetch(node.object_id, Float::INFINITY)
    end

    def subtree_end_position(item, node)
      return Float::INFINITY if node.nil?

      body_for(item)
      @subtree_end_cache.fetch(item.id, {}).fetch(node.object_id, Float::INFINITY)
    end

    def fallback_heading(item, doc)
      title = normalize_space(doc&.at_xpath("//*[local-name()='title']")&.text.to_s)
      return title unless title.empty?

      item_id = normalize_space(item.id.to_s)
      return item_id unless item_id.empty?

      normalize_space(item.href.to_s)
    end

    def clean_noise!(item, body)
      body.xpath(".//*").each do |node|
        next unless node.element?

        reason = removal_reason_for(node)
        next unless reason

        record_loss(
          "cleanup_removed_node",
          "Removed node during cleanup.",
          context: item_context(item).merge(
            reason: reason,
            path: safe_scalar(node.path),
            tag: node.name
          ),
          payload: safe_markup(node)
        )
        node.remove
      end
    end

    def removal_reason_for(node)
      tag = node.name.downcase
      return "unsupported_tag:#{tag}" if %w[script style noscript nav form canvas audio video svg].include?(tag)
      return "hidden_attribute" if hidden_attribute?(node)
      return "hidden_style" if style_hidden?(node)
      return "aria_hidden" if node["aria-hidden"].to_s.strip.downcase == "true"
      return "pagebreakish" if pagebreakish?(node)

      if %w[header footer].include?(tag)
        return nil if note_like?(node)

        return "header_footer"
      end

      label = [node["class"], node["id"]].compact.join(" ")
      return nil if label.empty?
      return nil if NOTE_PATTERN.match?(label)
      return "noise_pattern" if label.match?(NOISE_PATTERN)

      nil
    end

    def hidden_attribute?(node)
      node.key?("hidden") || node.key?("inert")
    end

    def style_hidden?(node)
      style = node["style"].to_s
      return false if style.empty?

      style.match?(HIDDEN_DECLARATION_PATTERN)
    end

    def note_like?(node)
      tokens = semantic_tokens(node)
      return true if note_tokens?(tokens)
      return true if note_attributes?(node)
      return true if note_reference_links?(node)

      text = normalize_space(node.text.to_s)
      return false if text.empty?
      return false unless note_listish?(node)
      return false unless text.length > 30

      starts_like_numbered_note?(text)
    end

    def semantic_tokens(node)
      [
        node.name,
        node["class"],
        node["id"],
        node["role"],
        namespaced_attribute(node, EPUB_NS, "type")
      ].compact.flat_map { |value| value.to_s.split(/\s+/) }
    end

    def note_tokens?(tokens)
      tokens.any? { |token| NOTE_PATTERN.match?(token) || NOTE_REF_PATTERN.match?(token) }
    end

    def note_attributes?(node)
      role = node["role"].to_s
      epub_type = namespaced_attribute(node, EPUB_NS, "type").to_s
      [role, epub_type].any? { |value| NOTE_PATTERN.match?(value) || NOTE_REF_PATTERN.match?(value) }
    end

    def note_reference_links?(node)
      node.xpath(".//*[self::a or self::aside or self::li or self::section or self::div]").any? do |descendant|
        next false unless descendant.element?

        descendant_tokens = semantic_tokens(descendant)
        href = descendant["href"].to_s
        role = descendant["role"].to_s
        epub_type = namespaced_attribute(descendant, EPUB_NS, "type").to_s

        note_tokens?(descendant_tokens) ||
          NOTE_PATTERN.match?(role) ||
          NOTE_PATTERN.match?(epub_type) ||
          NOTE_REF_PATTERN.match?(role) ||
          NOTE_REF_PATTERN.match?(epub_type) ||
          (href.start_with?("#") && (role.include?("doc-noteref") || descendant_tokens.any? { |token| token.include?("noteref") }))
      end
    end

    def note_listish?(node)
      node.element_children.any? { |child| %w[ol ul dl li aside section div p].include?(child.name.downcase) }
    end

    def starts_like_numbered_note?(text)
      text.match?(/\A(?:\[?\d+\]?|\(?\d+\)|\d+[\.:]|[*†‡§])\s+/)
    end

    def pagebreakish?(node)
      epub_type = namespaced_attribute(node, EPUB_NS, "type")
      role = node["role"].to_s
      tokens = (epub_type.to_s.split(/\s+/) + role.to_s.split(/\s+/)).reject(&:empty?)
      tokens.include?("pagebreak") || tokens.include?("page-list") || tokens.include?("doc-pagebreak") || tokens.include?("doc-pagelist")
    end

    def namespaced_attribute(node, namespace_uri, local_name)
      attr = node.attribute_nodes.find do |attribute|
        attribute.namespace&.href == namespace_uri && attribute.node_name.split(":").last == local_name
      end
      attr&.value
    end

    def nearest_block_or_heading(node, body)
      current = node
      while current && current != body
        return current if block_or_heading?(current)

        current = current.parent
      end
      body
    end

    def block_or_heading?(node)
      return false unless node.element?

      tag = node.name.downcase
      HTMLWalker::BLOCK_TAGS.include?(tag) || tag.match?(/\Ah[1-6]\z/)
    end

    def normalize_heading_levels!(events)
      levels = events.select { |event| event.type == :heading }.map(&:level).compact
      return if levels.empty?

      base = levels.min
      events.each do |event|
        next unless event.type == :heading

        event.level = (event.level - base) + 1
      end
    end

    def xpath_string(value)
      if value.include?("'")
        parts = value.split("'").map { |part| "'#{part}'" }
        %(concat(#{parts.join(%q{, "'", })}))
      else
        "'#{value}'"
      end
    end

    def render_loss_report
      return "" if @losses.empty?

      lines = []
      lines << "# Extraction diagnostics"
      lines << ""
      lines << "Detected skipped, removed, unresolved, or degraded content follows."
      lines << ""

      @losses.each_with_index do |loss, index|
        lines << "## Loss #{index + 1}: #{loss.category}"
        lines << loss.message

        loss.context.sort_by { |key, _| key.to_s }.each do |key, value|
          next if value.nil? || value.to_s.strip.empty?

          lines << "#{key}: #{safe_scalar(value)}"
        end

        unless loss.payload.to_s.empty?
          lines << ""
          lines << "```"
          lines.concat(safe_payload(loss.payload).split("\n"))
          lines << "```"
        end

        lines << ""
      end

      lines.join("\n")
    end

    def record_loss(category, message, context: {}, payload: nil)
      @losses << LossRecord.new(
        category: category,
        message: message,
        context: context.compact,
        payload: payload
      )
    end

    def item_context(item)
      {
        item_id: item&.id,
        href: item&.href,
        media_type: item.respond_to?(:media_type) ? item.media_type : nil
      }
    end

    def section_context(section)
      item_context(section.item).merge(
        section_text: section.text,
        fragment: section.fragment,
        depth: section.depth
      )
    end

    def safe_markup(node)
      safe_payload(node.to_xml)
    rescue StandardError
      safe_payload(node.text.to_s)
    end

    def safe_payload(value)
      value.to_s.encode("UTF-8", invalid: :replace, undef: :replace, replace: "")
    end

    def normalize_output(text)
      normalized = text
        .lines
        .map(&:rstrip)
        .join("\n")
        .gsub(/\n{3,}/, "\n\n")
        .strip

      normalized.empty? ? "" : normalized + "\n"
    end

    def safe_scalar(value)
      normalize_space(value.to_s)
    end

    def normalize_space(text)
      text
        .to_s
        .encode("UTF-8", invalid: :replace, undef: :replace, replace: "")
        .gsub(/[[:space:]]+/, " ")
        .strip
    end
  end

  class HTMLWalker
    BLOCK_TAGS = %w[
      address article aside blockquote body dd div dl dt figcaption figure li main
      ol p pre section table tbody td th thead tr ul
    ].to_set

    INLINE_SKIP_TAGS = %w[script style noscript nav].to_set

    def initialize(
      root,
      stop_at: nil,
      include_root: false,
      start_position: nil,
      stop_position: nil,
      position_lookup: nil,
      subtree_end_lookup: nil
    )
      @root = root
      @stop_at = stop_at
      @include_root = include_root
      @start_position = start_position
      @stop_position = stop_position
      @position_lookup = position_lookup
      @subtree_end_lookup = subtree_end_lookup
    end

    def events
      out = []

      if @include_root
        walk_single(@root, out, list_depth: 0)
      else
        walk_children(@root, out, list_depth: 0)
      end

      compact_paragraphs(out)
    end

    private

    def interval_mode?
      !@position_lookup.nil? && (!@start_position.nil? || !@stop_position.nil?)
    end

    def node_position(node)
      @position_lookup&.call(node)
    end

    def subtree_end_position(node)
      @subtree_end_lookup&.call(node)
    end

    def subtree_before_range?(node)
      return false unless interval_mode?
      return false if @start_position.nil?

      tail = subtree_end_position(node)
      !tail.nil? && tail < @start_position
    end

    def subtree_after_range?(node)
      return false unless interval_mode?
      return false if @stop_position.nil?

      head = node_position(node)
      !head.nil? && head >= @stop_position
    end

    def subtree_overlaps_range?(node)
      !subtree_before_range?(node) && !subtree_after_range?(node)
    end

    def node_fully_selected?(node)
      return true unless interval_mode?

      head = node_position(node)
      tail = subtree_end_position(node)

      start_ok = @start_position.nil? || head.nil? || head >= @start_position
      stop_ok = @stop_position.nil? || tail.nil? || tail < @stop_position
      start_ok && stop_ok
    end

    def stop_node?(node)
      return true if !@stop_at.nil? && node == @stop_at
      return true if subtree_after_range?(node)

      false
    end

    def walk_single(node, out, list_depth:)
      return if node.nil?
      return if subtree_before_range?(node)
      return if stop_node?(node)

      if node.comment?
        return
      elsif node.text?
        text = normalize_inline(node.text.to_s)
        out << Event.new(type: :paragraph, text: text) unless text.empty?
        return
      end

      pending_inline = []
      walk_node(node, pending_inline, out, list_depth: list_depth)
      flush_pending_inline!(pending_inline, out)
    end

    def walk_children(node, out, list_depth:)
      pending_inline = []

      node.children.each do |child|
        next if subtree_before_range?(child)
        break if stop_node?(child)

        if child.comment?
          next
        elsif child.text?
          pending_inline << child.text
          next
        end

        walk_node(child, pending_inline, out, list_depth: list_depth)
      end

      flush_pending_inline!(pending_inline, out)
    end

    def walk_node(node, pending_inline, out, list_depth:)
      return unless node.element?
      return unless subtree_overlaps_range?(node)

      tag = node.name.downcase
      return if INLINE_SKIP_TAGS.include?(tag)

      case tag
      when /\Ah([1-6])\z/
        flush_pending_inline!(pending_inline, out)
        text = inline_text(node)
        out << Event.new(type: :heading, level: Regexp.last_match(1).to_i, text: text) unless text.empty?

      when "ul", "ol"
        flush_pending_inline!(pending_inline, out)
        walk_list(node, out, list_depth: list_depth + 1)

      when "blockquote"
        flush_pending_inline!(pending_inline, out)

        if node_fully_selected?(node)
          quote = inline_text(node)
          if quote.empty?
            walk_children(node, out, list_depth: list_depth)
          else
            out << Event.new(type: :blockquote, text: quote)
          end
        else
          walk_children(node, out, list_depth: list_depth)
        end

      when "pre"
        flush_pending_inline!(pending_inline, out)
        text =
          if node_fully_selected?(node)
            node.text.to_s.encode("UTF-8", invalid: :replace, undef: :replace, replace: "")
          else
            inline_text(node)
          end
        out << Event.new(type: :preformatted, text: text.rstrip) unless text.strip.empty?

      else
        block_children = node.element_children.select do |child|
          subtree_overlaps_range?(child) &&
            (BLOCK_TAGS.include?(child.name.downcase) || child.name.downcase.match?(/\Ah[1-6]\z/))
        end

        if block_children.empty?
          if node_fully_selected?(node)
            pending_inline << inline_text(node)
          else
            walk_children(node, out, list_depth: list_depth)
          end
        else
          flush_pending_inline!(pending_inline, out)
          walk_children(node, out, list_depth: list_depth)
        end
      end
    end

    def walk_list(list_node, out, list_depth:)
      list_node.element_children.each do |child|
        next if subtree_before_range?(child)
        break if stop_node?(child)
        next unless child.name.downcase == "li"

        intro = inline_text_without_nested_lists(child)
        out << Event.new(type: :list_item, depth: list_depth, text: intro) unless intro.empty?

        child.xpath("./*[local-name()='ul' or local-name()='ol']").each do |nested|
          next if subtree_before_range?(nested)
          break if stop_node?(nested)

          walk_list(nested, out, list_depth: list_depth + 1)
        end

        child.element_children.each do |sub|
          next if subtree_before_range?(sub)
          break if stop_node?(sub)
          next if %w[ul ol].include?(sub.name.downcase)
          next unless sub.name.downcase.match?(/\Ah[1-6]\z/) || BLOCK_TAGS.include?(sub.name.downcase)

          walk_children(sub, out, list_depth: list_depth)
        end
      end
    end

    def inline_text_without_nested_lists(node)
      copy = node.dup(1)
      copy.xpath("./*[local-name()='ul' or local-name()='ol']").remove
      inline_text(copy)
    end

    def inline_text(node)
      pieces = []
      gather_inline(node, pieces)
      normalize_inline(pieces.join)
    end

    def gather_inline(node, pieces)
      case node
      when Nokogiri::XML::Text
        pieces << node.text
      when Nokogiri::XML::Element
        tag = node.name.downcase
        return if INLINE_SKIP_TAGS.include?(tag)

        if tag == "br"
          pieces << "\n"
          return
        end

        if tag == "img"
          alt = node["alt"].to_s.strip
          pieces << alt unless alt.empty?
          return
        end

        node.children.each do |child|
          break if stop_node?(child)
          next if subtree_before_range?(child)

          gather_inline(child, pieces)
        end
      end
    end

    def normalize_inline(text)
      text = CGI.unescapeHTML(text)
      lines = text
        .encode("UTF-8", invalid: :replace, undef: :replace, replace: "")
        .split(/\n+/)
        .map { |line| line.gsub(/[[:space:]]+/, " ").strip }
        .reject(&:empty?)
      lines.join("\n")
    end

    def flush_pending_inline!(pending_inline, out)
      text = normalize_inline(pending_inline.join(" "))
      out << Event.new(type: :paragraph, text: text) unless text.empty?
      pending_inline.clear
    end

    def compact_paragraphs(events)
      compacted = []
      events.each do |event|
        if event.type == :paragraph && compacted.last&.type == :paragraph
          compacted.last.text = [compacted.last.text, event.text].join("\n\n")
        else
          compacted << event
        end
      end
      compacted
    end
  end
end

EpubStructuredText::CLI.run(ARGV)
