import Text.Printf (printf)
import System.IO
import System.Environment
import Data.List
import Data.Maybe

toMarkdown :: String -> String
toMarkdown = unlines . stripPrefixD . foldl step ([blockstart] :: [String]) . lines
  where
    stripPrefixD s =
      let s' = stripPrefix [blockstart, blockend] s in
        fromMaybe s s'
    blockstart = "```lean"
    blockend   = "```"
    step acc line
      | take 2 line == "-/" = acc ++ [blockstart]
      | take 2 line == "/-" = acc ++ [blockend]
      | otherwise           = acc ++ [line]

main :: IO ()
main = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  getContents >>= (putStrLn . toMarkdown)

