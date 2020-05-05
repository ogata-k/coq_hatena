(* この中はコメント。(* 入れ子も可能 *)
  The Coq Proof Assistant, version 8.11.0 (January 2020)
  compiled on Jan 24 2020 22:35:23 with OCaml 4.07.1
*)

(*
  標準的に利用できるプリインライブラリや標準ライブラリは
    https://coq.inria.fr/doc/language/coq-library.html#thecoqlibrary
  を参照
*)
  
  (* 後で使うので、ペアノ算術を導入し自然数に関する公理を利用できるようにする *)
  Require Import Arith.
  
(* 
  意味のある区間をわかりやすくするためにセクションとして分割する。必須ではない。 
*)
Section introduction.
  (* 
    文脈(処理系)操作にはコマンド群のVernacular(ヴァーナキュラー)が使われる。
    Vernacularは大文字から始まる文でピリオド（.）で終わる。
    例： Section introduction.
    他にも以下のようなものがある。
    * 計算して評価せよという命令（Eval compute in）
    * 非再帰的関数を定義(Definition)
  *)
  Eval compute in ((fun (n:nat) => n * 2) 2).
  Definition double: nat->nat := fun (n:nat) => n * 2.

  (* 
    定理を定義して証明する。Propは命題型。bool型ではない。
    
    p /\ qのように数式風に書くこともできるし、and p qのように関数的に書くこともできる。 
    定義するのは簡単でor(\/)を結合優先度50の|_|演算子による中置演算子表記で置き換えるには以下のように記述
    
      Notation "p '|_|' q" := (or p q) (at level 50).
  *)
  Theorem and_r_or_desc:
    forall p q r: Prop, (p /\ q) \/ r <-> (p \/ r)  /\ (q \/ r).
  Proof.
    (* 証明図のならばの仮定のように消去できるようにするため仮定として持ち上げる *)
    intros P Q R.
    (* 両方向を示すために分割する *)
    split.
    (* (P /\ Q) \/ R -> (P \/ R) /\ (Q \/ R) *)
    - intro pq_r.
      (* 仮定pq_rに対して条件分岐 *)
      elim pq_r.
      
      (* P /\ Q -> (P \/ R) /\ (Q \/ R) *)
      -- intros pq.
         (* 束縛された命題であったPやQを仮定として使えるものになったので、P/\Qを分割しつつ新たにPをp, Qをqと名付ける *)
         elim pq; intros p q.
         (* 分割しながら両項それぞれ左の項を選択して仮定より成り立つことを言う *)
         split; left; assumption.
      
      (* R -> (P \/ R) /\ (Q \/ R) *)
      -- intro r.
         (* 先ほどと同様にassumptionでもいいが、今回は仮定rと一致しているので明示的に指定 *)
         split; right; apply r.
      
   (* 逆向き。 (P \/ R) /\ (Q \/ R) -> (P /\ Q) \/ R *)
   - intro pr_qr.
     elim pr_qr.
     intros pr qr.
     (* 愚直にP, Q, Rを場合分け。 introsで指定されている命題がそれぞれ真の場合で進行 *)
     elim pr; elim qr.
     (* Q -> P -> P /\ Q \/ R *)
     -- intros q p.
        left.
        split; assumption.
     (* R -> P -> P /\ Q \/ R *)
     -- intros r p.
        right.
        exact r.
     (* Q -> R -> P /\ Q \/ R *)
     -- intros q r.
        right.
        exact r.
     (* R -> R -> P /\ Q \/ R *)
     -- intros r _.
        right.
        exact r.
  Qed.  (* 証明できた *)
  
  (* 証明できたのでこの証明を構築するための関数が実装されている。それを確認する *)
  Print and_r_or_desc.
  (* 試しに計算してみる *)
  Print True.
  Print False. (* Coqでは~PはPの否定で、FalseはP/\~Pと同じ。 つまり矛盾のこと *)
  (* 代入する。命題なので単純化はされない。 *)
  Eval compute in (and_r_or_desc True False False).
  (* 計算が通ることを確認するCheckでも同じ結果が得られる *)
  Check (and_r_or_desc True False False).


  Section monoid.
    (* インスタンスを作る構造を定義 *)
    Class Monoid M := monoid{
       (* 持っていてほしい情報 *)
       op : M -> M -> M;
       e : M;
       
       (* 公理 *)
       assoc: forall a b c : M, (op (op a b) c) = (op a (op b c));
       e_l: forall a: M, op e a = a;
       e_r: forall a: M, op a e = a;
    }.
    Print e.
    
    Program Instance nat_monoid : Monoid nat := {|
      op := fun m n => m + n;
      e := 0;
      assoc:= plus_assoc_reverse;
      e_l:= Nat.add_0_l;
      e_r:= Nat.add_0_r;
    |}.
    
    
    (* Haskellのようなフィールド組として扱いたいとき。Recordの代わりにStructureでも可 *)
    Record ToNatConvertrt (T: Type): Type := converter{first: T -> T; second: T -> T}.
    Print converter.
    Check (converter nat).
    (* 本来なら関数定義通りに上記のようにnatという型を教えてあげる必要があるが、Argumentsによってそれを省略するように指定する *)
    Arguments converter [T] _.
    Check converter.
    Check (fun n: Monoid nat => op n n).
    Eval compute in ( converter (fun n: Monoid nat => e) (fun n: Monoid nat => op n n) ).
  End monoid.
End  introduction.
