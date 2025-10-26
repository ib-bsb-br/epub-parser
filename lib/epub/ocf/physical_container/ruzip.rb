require "ruzip"

module EPUB
  class OCF
    class PhysicalContainer
      class RuZip < self
        def open
          @monitor.synchronize do
            @archive = ::RuZip::Archive.new(@container_path)
            begin
              yield self
            ensure
              @archive = nil
            end
          end
        end

        def read(path_name)
          if @archive
            file = @archive.by_name(path_name)
            raise NoEntry.new(path_name) unless file

            file.read
          else
            open {|container| container.read(path_name)}
          end
        end
      end
    end
  end
end
