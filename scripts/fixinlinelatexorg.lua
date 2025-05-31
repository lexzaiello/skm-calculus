function RawInline(elem)
  if elem.format == 'latex' then
    -- Replace \( ... \) with $...$
    local stripped = elem.text:match("^\\%((.-)\\%)$")
    if stripped then
      return pandoc.RawInline('markdown', '$' .. stripped .. '$')
    end
  end
end