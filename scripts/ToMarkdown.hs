import Text.Printf (printf)
import System.IO
import System.Environment

toMarkdown :: String -> String
toMarkdown = unlines . snd . foldl step (False, ([] :: [String])) . lines
  where
    step (isLean, acc) line
      | take 3 line == "--/" = (True, acc ++ ["```lean", drop 3 line])
      | take 3 line == "/--" = (False, acc ++ [drop 3 line, "```"])
      | otherwise            = (isLean, acc ++ [line])

main :: IO ()
main = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  getContents >>= (putStrLn . toMarkdown)

