# ipc-hs
## これはなに
- Haskellで書かれた直観主義命題論理の自動証明器です
- `ipc-hs-exe2`に`input.txt`を食わせたところ、
  - すべての行について証明を生成/断念するのが合計1.5秒程度で終了し
  - 先駆者qnighyさんの https://github.com/qnighy/logic-solver-rs で証明できた物はすべて証明できました
- たぶん実用的な速度で正確に動くと思います

## 動作環境
- stack(Haskellのビルドツール)が必要です。持ってなかったら[GHCup](https://www.haskell.org/ghcup/)(Haskellのツール管理ツール)とかで入れてください

## つかいかた
- `stack run ipc-hs-exe [-v | -l | -lv] 論理式` : 証明図を出力します
  - `-l`, `-lv` : 証明図のかわりにラムダ式を出力します。
  - `-v`, `-lv` : 証明探索中のログを合わせて出力します。 __論理式によっては出力が100MBを超えることがあります__
- `stack run ipc-hs-exe2 ファイル` : 指定のファイルの各行について証明の可否を出力します。具体的に、`input.txt`を食わせると`result.txt`が出てきます