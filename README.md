# Hindley-Milner type inference

みなさん、ﾊﾟｿｶﾀしてますか〜？
私はパソ型してます。

## What is this?

Hindley-Milnerの型推論器の実装です。

前後の文脈から型の制約を抽出して双方向に型推論を行う場合の実装の基礎理論としてHindley-Milnerの理論があり、
そのうち、型の制約の集合において型変数の単一化(_unification_)と代入(_substitution_)を交互に行う*algorithm W*に相当する実装を行いました。
