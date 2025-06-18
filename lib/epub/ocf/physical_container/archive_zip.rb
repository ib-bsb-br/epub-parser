require 'archive/zip'

module EPUB
  class OCF
    class PhysicalContainer
      class ArchiveZip < self
        def initialize(container_path)
          super
          @entries = {}
          @last_iterated_entry_index = 0
        end

        def open
          Archive::Zip.open @container_path do |archive|
            @monitor.synchronize do
              @archive = archive
              begin
                yield self
              ensure
                @archive = nil
              end
            end
          end
        end

        def read(path_name)
          if @archive
            target_index = @entries[path_name]
            @archive.each.with_index do |entry, index|
              if target_index
                if target_index == index
                  return read_content(entry)
                else
                  next
                end
              end
              next if index < @last_iterated_entry_index
              # We can force encoding UTF-8 because EPUB spec allows only UTF-8 filenames
              entry_path = entry.zip_path.force_encoding('UTF-8')
              @entries[entry_path] = index
              @last_iterated_entry_index = index
              if entry_path == path_name
                return read_content(entry)
              end
            end

            raise NoEntry, "Entry not found: #{path_name}"
          else
            open {|container| container.read(path_name)}
          end
        end

        private

        def read_content(entry)
          file_data = entry.file_data
          content = ""
          begin
            loop do
              content << file_data.read(8192)
            end
          rescue EOFError
          end
          content
        end
      end
    end
  end
end
