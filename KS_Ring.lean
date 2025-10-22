/-
Copyright (c) 2025 Katabami Shu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katabami Shu, Patrick Massot
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Tactic.Spread
import Mathlib.Util.AssertExists
import Mathlib.Tactic.StacksAttribute
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Ring.Pi

--Ringを構成しているclassを導入

/-
class Distrib (R : Type*) extends Mul R, Add R where
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
-/

--ここからℤ[√5]の構成

structure ZRootFive where
    re : ℤ
    im : ℤ
deriving Repr, DecidableEq, Inhabited, BEq

--演算と単位元・逆元の定義

instance : Add ZRootFive where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

instance : Zero ZRootFive where
  zero := ⟨0, 0⟩

instance : Neg ZRootFive where
  neg x := ⟨-x.re, -x.im⟩

instance : Sub ZRootFive where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

instance : Mul ZRootFive where
  mul x y :=
    ⟨x.re * y.re + 5 * x.im * y.im, x.re * y.im + x.im * y.re⟩

instance : One ZRootFive where
  one := ⟨1, 0⟩

--整数倍を定義
def ZRootFive.zsmulFun (z : Int) (a : ZRootFive) : ZRootFive :=
  match z with
  | Int.ofNat n   => nsmulRec n a
  | Int.negSucc n => -(nsmulRec (n + 1) a)

--定義通りの計算と外延性をコマンドで呼び出す準備

@[simp]
theorem ZRootFive.add_def (a b : ZRootFive) :
    a + b = ⟨a.re + b.re, a.im + b.im⟩ := rfl

@[simp]
theorem ZRootFive.zero_def : (0 : ZRootFive) = ⟨0, 0⟩ := rfl

@[simp]
theorem ZRootFive.neg_def (a : ZRootFive) :
    -a = ⟨-a.re, -a.im⟩ := rfl

@[simp]
theorem ZRootFive.mul_def (a b : ZRootFive) :
    a * b = ⟨a.re * b.re + 5 * a.im * b.im, a.re * b.im + a.im * b.re⟩ := rfl

@[simp]
theorem ZRootFive.one_def : (1 : ZRootFive) = ⟨1, 0⟩ := rfl

@[ext]
theorem ZRootFive.ext {a b : ZRootFive} (h₁ : a.re = b.re) (h₂ : a.im = b.im) : a = b := by
  cases a
  cases b
  simp_all

--ℤ[√5]が環の定義を満たすことの証明

namespace ZRootFive

instance : Ring ZRootFive where
  --加法の結合則
    add_assoc := by
      intros a b c
      ext <;> simp [ZRootFive.add_def, add_assoc]
      case h₁ => exact Int.add_assoc a.re b.re c.re
      case h₂ => exact Int.add_assoc a.im b.im c.im
  --a+0=0+a=a
    zero_add := by
      intro a
      ext
      case h₁ => exact Int.zero_add a.re
      case h₂ => exact Int.zero_add a.im
    add_zero := by
      intros a
      ext
      case h₁ => exact Int.add_zero a.re
      case h₂ => exact Int.add_zero a.im
  --自然数の積
    nsmul := by
      exact nsmulRec
  --加法の交換
    add_comm := by
      intros a b
      ext
      case h₁ => exact Int.add_comm a.re b.re
      case h₂ => exact Int.add_comm a.im b.im
  --左からの分配
    left_distrib := by
      intros a b c
      ext
      case h₁ =>
        simp [ZRootFive.mul_def, ZRootFive.add_def]
        calc
            a.re * (b.re + c.re) + 5 * a.im * (b.im + c.im)
              = (a.re * b.re + a.re * c.re) + (5 * a.im * b.im + 5 * a.im * c.im) := by
                rw [Int.mul_add, Int.mul_add]
            _ = a.re * b.re + a.re * c.re + 5 * a.im * b.im + 5 * a.im * c.im := by
                rw [←Int.add_assoc]
            _ = a.re * b.re + (a.re * c.re + 5 * a.im * b.im) + 5 * a.im * c.im := by
                rw [← Int.add_assoc]
            _ = a.re * b.re + (5 * a.im * b.im + a.re * c.re) + 5 * a.im * c.im := by
                rw [Int.add_comm (a.re * c.re) (5 * a.im * b.im)]
            _ = (a.re * b.re + 5 * a.im * b.im) + (a.re * c.re + 5 * a.im * c.im) := by
                rw [← Int.add_assoc]
                rw [Int.add_assoc]
      case h₂ =>
        simp [ZRootFive.mul_def, ZRootFive.add_def]
        calc
            a.re * (b.im + c.im) + a.im * (b.re + c.re)
              = (a.re * b.im + a.re * c.im) + (a.im * b.re +  a.im * c.re) := by
                rw [Int.mul_add, Int.mul_add]
            _ = a.re * b.im + a.re * c.im + a.im * b.re + a.im * c.re := by
                rw [←Int.add_assoc]
            _ = a.re * b.im + (a.re * c.im + a.im * b.re) + a.im * c.re := by
                rw [← Int.add_assoc]
            _ = a.re * b.im + (a.im * b.re + a.re * c.im) + a.im * c.re := by
                rw [Int.add_comm (a.im * b.re) (a.re * c.im)]
            _ = a.re * b.im + a.im * b.re + (a.re * c.im + a.im * c.re) := by
                rw [← Int.add_assoc]
                rw [Int.add_assoc]
  --右からの分配
    right_distrib := by
      intros a b c
      ext
      case h₁ =>
        simp [ZRootFive.mul_def, ZRootFive.add_def]
        calc (a.re + b.re) * c.re + 5 * (a.im + b.im) * c.im
            = a.re * c.re + b.re * c.re + 5 * a.im * c.im + 5 *b.im * c.im := by
              rw [Int.add_mul, Int.mul_add, Int.add_mul]
              rw [← Int.add_assoc]
          _ = a.re * c.re + (b.re * c.re + 5 * a.im * c.im) + 5 * b.im * c.im := by
              rw [← Int.add_assoc]
          _ = a.re * c.re + (5 * a.im * c.im + b.re * c.re) + 5 * b.im * c.im := by
              rw [Int.add_comm (b.re * c.re) (5 * a.im * c.im)]
          _ = a.re * c.re + 5 * a.im * c.im + (b.re * c.re + 5 * b.im * c.im) := by
              rw [←Int.add_assoc, Int.add_assoc]
      case h₂ =>
        simp [ZRootFive.mul_def, ZRootFive.add_def]
        calc (a.re + b.re) * c.im + (a.im + b.im) * c.re
            = a.re * c.im + b.re * c.im + a.im * c.re + b.im * c.re := by
              rw [Int.add_mul, Int.add_mul]
              rw [← Int.add_assoc]
          _ = a.re * c.im + (b.re * c.im + a.im * c.re) + b.im * c.re := by
              rw [← Int.add_assoc]
          _ = a.re * c.im + (a.im * c.re + b.re * c.im) + b.im * c.re := by
              rw [Int.add_comm (b.re * c.im) (a.im * c.re)]
          _ = a.re * c.im + a.im * c.re + (b.re * c.im + b.im * c.re) := by
              rw [←Int.add_assoc, Int.add_assoc]
--0*a=a*0=0
    zero_mul := by
      intros a
      ext
      case h₁ =>
        simp [ZRootFive.mul_def]
      case h₂ =>
        simp [ZRootFive.mul_def]
    mul_zero := by
      intros a
      ext
      case h₁ =>
        simp [ZRootFive.mul_def]
      case h₂ =>
        simp [ZRootFive.mul_def]
--乗法の結合則
    mul_assoc := by
      intros a b c
      ext
      case h₁ =>
          simp [ZRootFive.mul_def]
          calc (a.re * b.re + 5 * a.im * b.im) * c.re + 5 * (a.re * b.im + a.im * b.re) * c.im
              = a.re * b.re * c.re + 5 * a.im * b.im * c.re + 5 * a.re * b.im * c.im + 5 * a.im * b.re * c.im := by
                rw [Int.add_mul, Int.mul_add, Int.add_mul]
                rw [←Int.add_assoc, ←Int.mul_assoc, ←Int.mul_assoc]
            _ = a.re * (b.re * c.re + 5 * b.im * c.im) + 5 * a.im * (b.re * c.im + b.im * c.re) := by
                rw [Int.mul_assoc]
                rw [Int.add_assoc, Int.add_assoc, ←Int.add_assoc (5 * a.im * b.im * c.re), ←Int.add_assoc]
                rw [Int.add_comm (5 * a.im * b.im * c.re) (5 * a.re * b.im * c.im)]
                rw [Int.add_assoc, Int.add_assoc, ←Int.add_assoc]
                rw [Int.mul_comm 5 a.re, Int.mul_comm 5 a.im]
                rw [Int.mul_assoc, Int.mul_assoc, ←Int.mul_assoc 5]
                rw [←Int.mul_add a.re (b.re * c.re) (5 * b.im * c.im)]
                rw [←Int.add_assoc]
                rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
                rw [←Int.mul_assoc 5, ←Int.mul_assoc 5, ←Int.mul_assoc 5]
                rw [Int.add_assoc]
                rw [←Int.mul_add a.im (5 * b.im * c.re) (5 * b.re * c.im)]
                rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
                rw [←Int.mul_add 5 (b.im * c.re) (b.re * c.im)]
                rw [←Int.mul_assoc, ←Int.mul_assoc, Int.mul_comm a.im]
                rw [Int.add_comm (b.re * c.im) (b.im * c.re)]
      case h₂ =>
          simp [ZRootFive.mul_def]
          calc (a.re * b.re + 5 * a.im * b.im) * c.im + (a.re * b.im + a.im * b.re) * c.re
              = a.re * b.re * c.im + 5 * a.im * b.im * c.im + a.re * b.im * c.re + a.im * b.re * c.re := by
                rw [Int.add_mul, Int.add_mul]
                rw [←Int.add_assoc]
            _ = a.re * (b.re * c.im + b.im * c.re) + a.im * (5 * b.im * c.im + b.re * c.re) := by
                rw [Int.mul_assoc]
                rw [Int.add_assoc, Int.add_assoc, ←Int.add_assoc (5 * a.im * b.im * c.im), ←Int.add_assoc]
                rw [Int.add_comm (5 * a.im * b.im * c.im) (a.re * b.im * c.re)]
                rw [Int.add_assoc, Int.add_assoc, ←Int.add_assoc]
                rw [Int.mul_comm 5 a.im]
                rw [Int.mul_assoc, Int.mul_assoc]
                rw [←Int.mul_add a.re (b.re * c.im) (b.im * c.re)]
                rw [←Int.add_assoc]
                rw [Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
                rw [←Int.mul_assoc 5]
                rw [Int.add_assoc]
                rw [←Int.mul_add a.im (5 * b.im * c.im) (b.re * c.re)]
            _ = a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re + 5 * b.im * c.im) := by
                rw [Int.add_comm (5 * b.im * c.im) (b.re * c.re)]
--1*a=a*1=a
    one_mul := by
      intro a
      ext
      case h₁ =>
        simp [ZRootFive.mul_def]
      case h₂ =>
        simp [ZRootFive.mul_def]
    mul_one := by
      intro a
      ext
      case h₁ =>
        simp [ZRootFive.mul_def]
      case h₂ =>
        simp [ZRootFive.mul_def]
--整数倍
    zsmul := by exact
      ZRootFive.zsmulFun
--加法についてある元とその逆元の和
    neg_add_cancel := by
      intro a
      ext
      case h₁ =>
        simp [ZRootFive.mul_def]
        rw [Int.add_left_neg]
      case h₂ =>
        simp [ZRootFive.mul_def]
        rw [Int.add_left_neg]

--以上に追加して可換であることを示せばℤ[√5]はCommRing

--class CommRing (α:Type u) extends Ring α, CommMonoid α : Type u

--CommRingが可換であることを読み込むため、可換マグマ(閉じた演算を持つ集合で可換であるもの)を定義
--ZRootFiveの定義からℤがCommRingであることを利用
--和のマグマ
instance : AddCommMagma ℤ :=
{ add_comm := Int.add_comm }

--積のマグマ
instance : CommMagma ZRootFive :=
{ mul_comm := by
    intros a b
    ext
    case h₁ =>
      rw [ZRootFive.mul_def, ZRootFive.mul_def]
      rw [Int.mul_comm, Int.mul_assoc, Int.mul_comm a.im b.im, ←Int.mul_assoc]
    case h₂ =>
      rw [ZRootFive.mul_def, ZRootFive.mul_def]
      rw [Int.mul_comm, Int.mul_assoc]
      rw [Int.mul_comm b.re a.im, Int.mul_comm b.im a.re]
      rw [Int.mul_comm a.im b.im, ←Int.mul_assoc]
      rw [add_comm (a.im * b.re) (a.re * b.im)]
}

--ZRootFiveが可換であることはCommMagmaであることから直ちに従う
instance : CommRing ZRootFive where
  toRing := (by infer_instance : Ring ZRootFive)
  mul_comm := by
    intros a b
    rw [mul_comm]

--次に、ℤ³[√5]がRingであることを示す
--ℤ[√5]と同様に示すと計算量が膨大に->証明済みのℤ[√5]を利用して証明

--(0, 1, 2)の添字に(x₀, x₁, x₂)と割り当てて数字の組を作る。この数字の組をZRootFive3として定義

def ZRootFive3 := Fin 3 → ZRootFive

/-Fin 3に与えられた値がそれぞれCommRingの値であれば、
各部分でCommRingであるため像もCommRingであることを@Pi.commRingが示している-/

/-inferInstanceは対象としているclassについて型推論を行い、任意の値を合成する-/
instance : CommRing ZRootFive3 :=
  @Pi.commRing (Fin 3) (fun _ => ZRootFive) (fun _ => inferInstance)
