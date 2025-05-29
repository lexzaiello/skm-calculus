import Text.Printf (printf)
import System.IO
import System.Environment

toMarkdown :: String -> String
toMarkdown = unlines . snd . foldl step (True, (["```lean"] :: [String])) . lines
  where
    step (isLean, acc) line
      | take 3 line == "--/" = (True, acc ++ ["```lean"])
      | take 3 line == "/--" = (False, acc ++ ["```"])
      | otherwise            = (isLean, acc ++ [line])

main :: IO ()
main = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  getContents >>= (putStrLn . toMarkdown)

