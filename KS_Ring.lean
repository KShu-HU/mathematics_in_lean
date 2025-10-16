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

--Ringを構成しているclassを導入

class Distrib (R : Type*) extends Mul R, Add R where
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R

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

instance : Ring ZRootFive where
  --結合則
    add_assoc := by
      intros a b c
      ext <;> simp [ZRootFive.add_def, add_assoc]
      case h₁ => exact Int.add_assoc a.re b.re c.re
      case h₂ => exact Int.add_assoc a.im b.im c.im
  --加法単位元
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
  --
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
    mul_assoc := by
      intros a b c
      ext
      case h₁ =>
          simp [ZRootFive.mul_def]
          calc (a.re * b.re + 5 * a.im * b.im) * c.re + 5 * (a.re * b.im + a.im * b.re) * c.im
              = a.re * b.re * c.re + 5 * a.im * b.im * c.re + 5 * a.re * b.im * c.im + 5 * a.im * b.re * c.im := by
                rw []
                /-rw [Int.add_mul, Int.mul_add, Int.add_mul]
                rw [←Int.add_assoc, ←Int.mul_assoc, ←Int.mul_assoc]-/
            _ = a.re * b.re * c.re + 5 * a.im * b.im * c.re + 5 * a.re * b.im * c.im + 5 * a.im * b.re * c.im := by
                rfl
      next => rw []

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
    zsmul := by sorry
    neg_add_cancel := by
      intro a
      ext
      case h₁ =>
        simp [ZRootFive.mul_def]
        rw [Int.add_comm]
      case h₂ =>
        simp [ZRootFive.mul_def]



--以上に追加して可換であることを示せばℤ[√5]はCommRing

class CommRing (α:Type u) extends Ring α, CommMonoid α : Type u

instance : CommRing ZRootFive where
  mul_com := by sorry

--次に、ℤ³[√5]がRingであることを示す
--ℤ[√5]と同様に示すと計算量が膨大に->準同型定理を利用
--準同型写像f:ℤ[√5]→ℤ³[√5]を用いてℤ[√5]/Ker(f)とℤ³[√5]が同型であることを示す方針
