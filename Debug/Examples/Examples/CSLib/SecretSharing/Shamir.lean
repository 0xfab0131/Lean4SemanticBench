import Cslib.Crypto.Protocols.SecretSharing.Shamir

/-!
# お題: 秘密分散（cslib）の入口

解析の対象は cslib 側のモジュール `Cslib.Crypto.Protocols.SecretSharing.*`
（`Scheme`: 方式の構文・正しさ・視点の識別不能性、`Defs`: 共有分布・視点分布・事後分布・
完全秘匿、`Shamir`: Shamir 法、`Shamir.Polynomial`: Lagrange 補間による再構成）。
宣言はそこに在る。

このファイルは `lake build Examples` でそれらのモジュールをビルドさせるための入口で、
宣言は持たない（`Shamir` は `Scheme` / `Defs` / `Shamir.Polynomial` を推移的に import する）。
-/
