import Text.Printf (printf)
import System.IO
import System.Environment
import Data.List
import Data.Maybe

blockstart = "```lean"
blockend   = "```"
mkfooter s = s ++ "/-\nMade by [<b>Alexandra Zaldivar Aiello</b>](https://github.com/lexzaiello).\n-/"

step ::[String] -> [String]
step [] = []
step s =
  let lean = ((takeWhile (/= "-/")) . (takeWhile (/= "/-"))) s; md = drop (length lean) s; in
      if md == s then
        let md = ((dropWhile (== "/-")) . (takeWhile (/= "-/"))) s; lean = drop ((length md) + 1) s in
          md ++ step lean
      else
        [blockstart] ++ lean ++ [blockend] ++ step md

toMarkdown :: String -> String
toMarkdown = unlines . step . lines . mkfooter

main :: IO ()
main = do
  hSetEncoding stdin utf8
  hSetEncoding stdout utf8
  getContents >>= (putStrLn . toMarkdown)

