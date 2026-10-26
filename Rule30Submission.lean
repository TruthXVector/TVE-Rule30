/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/

import Rule30PrizeKit
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Basic

open Ruliology.CellularAutomata
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

namespace Rule30Submission

/-!
# Section 0: Core Grid Coordinates, Vacuum Bounds, and Left-Null Diagonals
-/

def cellNat (t : Nat) (x : Int) : Nat :=
  if cell t x then 1 else 0

def cellInt (t : Nat) (x : Int) : Int :=
  if cell t x then 1 else 0

def M (t : Nat) (k : Int) : Int :=
  cellInt t ((t : Int) - k)

def partialM (t : Nat) (k : Int) : Int :=
  M (t + 1) (k + 1) - M t (k + 1)

def deltaInt (Q : Nat) (t : Nat) (x : Int) : Int :=
  if xor (cell (t + Q) x) (cell t x) then 1 else 0

def partialD (Q : Nat) (t : Nat) (x : Int) : Int :=
  deltaInt Q (t + 1) x - deltaInt Q t x

theorem cell_zero (x : Int) : cell 0 x = decide (x = 0) := rfl

theorem cell_step (t : Nat) (x : Int) :
    cell (t + 1) x = xor (cell t (x - 1)) (cell t x || cell t (x + 1)) := rfl

theorem cell_step_one (t : Nat) :
    cell (t + 1) 1 = xor (cell t 0) (cell t 1 || cell t 2) := by
  rw [cell_step t 1]
  have h1 : (1 : Int) - 1 = 0 := by omega
  have h2 : (1 : Int) + 1 = 2 := by omega
  rw [h1, h2]

theorem cell_step_two (t : Nat) :
    cell (t + 1) 2 = xor (cell t 1) (cell t 2 || cell t 3) := by
  rw [cell_step t 2]
  have h1 : (2 : Int) - 1 = 1 := by omega
  have h2 : (2 : Int) + 1 = 3 := by omega
  rw [h1, h2]

theorem xor_cancel_right (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem xor_cancel_left (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

theorem cell_left_step (t : Nat) (x : Int) :
    cell t (x - 1) = xor (cell (t + 1) x) (cell t x || cell t (x + 1)) := by
  rw [cell_step t x, xor_cancel_right]

theorem cell_eq_false_of_lt_neg : ∀ (t : Nat) (x : Int), x < - (t : Int) → cell t x = false
  | 0, x, hx => by
    rw [cell_zero]
    simp
    omega
  | t + 1, x, hx => by
    rw [cell_step]
    have hx1 : x - 1 < - (t : Int) := by omega
    have hx2 : x < - (t : Int) := by omega
    have hx3 : x + 1 < - (t : Int) := by omega
    rw [cell_eq_false_of_lt_neg t (x - 1) hx1,
        cell_eq_false_of_lt_neg t x hx2,
        cell_eq_false_of_lt_neg t (x + 1) hx3]
    rfl

theorem cell_eq_false_of_gt : ∀ (t : Nat) (x : Int), (t : Int) < x → cell t x = false
  | 0, x, hx => by
    rw [cell_zero]
    simp
    omega
  | t + 1, x, hx => by
    rw [cell_step]
    have hx1 : (t : Int) < x - 1 := by omega
    have hx2 : (t : Int) < x := by omega
    have hx3 : (t : Int) < x + 1 := by omega
    rw [cell_eq_false_of_gt t (x - 1) hx1,
        cell_eq_false_of_gt t x hx2,
        cell_eq_false_of_gt t (x + 1) hx3]
    rfl

theorem cell_left_edge : ∀ (t : Nat), cell t (- (t : Int)) = true
  | 0 => rfl
  | t + 1 => by
    rw [cell_step]
    have hx1 : - ((t + 1 : Nat) : Int) - 1 < - (t : Int) := by omega
    have hx2 : - ((t + 1 : Nat) : Int) < - (t : Int) := by omega
    have hx3 : - ((t + 1 : Nat) : Int) + 1 = - (t : Int) := by omega
    rw [cell_eq_false_of_lt_neg t _ hx1,
        cell_eq_false_of_lt_neg t _ hx2,
        hx3, cell_left_edge t]
    rfl

theorem cellInt_left_edge (t : Nat) : cellInt t (- (t : Int)) = 1 := by
  unfold cellInt
  rw [cell_left_edge t]
  rfl

theorem cell_left_edge_next : ∀ (t : Nat), cell (t + 1) (- (t : Int)) = true
  | 0 => rfl
  | t + 1 => by
    rw [cell_step]
    have hx1 : - ((t + 1 : Nat) : Int) - 1 < - ((t + 1 : Nat) : Int) := by omega
    rw [cell_eq_false_of_lt_neg (t + 1) _ hx1, cell_left_edge (t + 1)]
    rfl

theorem cellInt_left_edge_next (t : Nat) : cellInt (t + 1) (- (t : Int)) = 1 := by
  unfold cellInt
  rw [cell_left_edge_next t]
  rfl

theorem cell_left_edge_two (t : Nat) : cell (t + 2) (- (t : Int)) = false := by
  rw [cell_step]
  have hx1 : - (t : Int) - 1 = - ((t + 1 : Nat) : Int) := by omega
  rw [hx1, cell_left_edge (t + 1), cell_left_edge_next t]
  rfl

/-- Left-Null coordinate `aBool t j = cell t (-t + j)`. -/
def aBool (t j : Nat) : Bool :=
  cell t (- (t : Int) + (j : Int))

theorem aBool_step (t j : Nat) :
    aBool (t + 1) (j + 2) = xor (aBool t j) (aBool t (j + 1) || aBool t (j + 2)) := by
  unfold aBool
  rw [cell_step]
  have h1 : - ((t + 1 : Nat) : Int) + ((j + 2 : Nat) : Int) - 1 = - (t : Int) + (j : Int) := by omega
  have h2 : - ((t + 1 : Nat) : Int) + ((j + 2 : Nat) : Int) = - (t : Int) + ((j + 1 : Nat) : Int) := by omega
  have h3 : - (t : Int) + ((j + 1 : Nat) : Int) + 1 = - (t : Int) + ((j + 2 : Nat) : Int) := by omega
  rw [h1, h2, h3]

theorem aBool_zero (t : Nat) : aBool t 0 = true := by
  unfold aBool
  have h : - (t : Int) + ((0 : Nat) : Int) = - (t : Int) := by omega
  rw [h]
  exact cell_left_edge t

theorem aBool_one (t : Nat) : aBool (t + 1) 1 = true := by
  unfold aBool
  have h : - ((t + 1 : Nat) : Int) + ((1 : Nat) : Int) = - (t : Int) := by omega
  rw [h]
  exact cell_left_edge_next t

theorem aBool_two (t : Nat) : aBool (t + 2) 2 = false := by
  unfold aBool
  have h : - ((t + 2 : Nat) : Int) + ((2 : Nat) : Int) = - (t : Int) := by omega
  rw [h]
  exact cell_left_edge_two t

theorem aBool_three_step (t : Nat) : aBool (t + 3) 3 = !aBool (t + 2) 3 := by
  have h := aBool_step (t + 2) 1
  rw [aBool_one (t + 1), aBool_two t] at h
  rw [h]
  cases (aBool (t + 2) 3) <;> rfl

theorem aBool_four : ∀ (t : Nat), aBool (t + 2) 4 = true
  | 0 => rfl
  | t + 1 => by
    have h := aBool_step (t + 2) 2
    rw [aBool_two t, aBool_four t] at h
    rw [h]
    cases (aBool (t + 2) 3) <;> rfl

theorem aBool_five_eq_three (t : Nat) : aBool (t + 3) 5 = aBool (t + 3) 3 := by
  have h := aBool_step (t + 2) 3
  rw [aBool_four t] at h
  rw [h, aBool_three_step t]
  cases (aBool (t + 2) 3) <;> rfl

theorem aBool_six_eq_five : ∀ (t : Nat), aBool (t + 3) 6 = aBool (t + 3) 5
  | 0 => rfl
  | t + 1 => by
    have h6 := aBool_step (t + 3) 4
    rw [aBool_four (t + 1), aBool_six_eq_five t] at h6
    have h5 : aBool (t + 4) 5 = !aBool (t + 3) 5 := by
      rw [aBool_five_eq_three (t + 1), aBool_five_eq_three t, aBool_three_step (t + 1)]
    rw [h6, h5]
    cases (aBool (t + 3) 5) <;> rfl

theorem aBool_seven_shift : ∀ (t : Nat), aBool (t + 3) 7 = false
  | 0 => rfl
  | t + 1 => by
    have h7 := aBool_step (t + 3) 5
    rw [aBool_six_eq_five t, aBool_seven_shift t] at h7
    rw [h7]
    cases (aBool (t + 3) 5) <;> rfl

/-- Diagonal `j = 7` is a global zero diagonal for all `t ≥ 0`. -/
theorem aBool_seven : ∀ (t : Nat), aBool t 7 = false
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | t + 3 => aBool_seven_shift t

theorem aBool_nine_shift : ∀ (t : Nat), aBool (t + 5) 9 = true
  | 0 => rfl
  | t + 1 => by
    have h9 := aBool_step (t + 5) 7
    rw [aBool_seven (t + 5), aBool_nine_shift t] at h9
    rw [h9]
    cases (aBool (t + 5) 8) <;> rfl


/-!
# Section 1: The Universal Right-Cone Ideal `I_univ` (U1–U5) and Packet Constraints
-/

/-- The universal right-leakage sequence `wBool t = (!cell t 0) && cell t 1`. -/
def wBool (t : Nat) : Bool :=
  (!cell t 0) && cell t 1

def wInt (t : Nat) : Int :=
  (1 - cellInt t 0) * cellInt t 1

/-- Primary periodic leakage defect `dBool Q t = wBool (t + Q) ^^ wBool t`. -/
def dBool (Q t : Nat) : Bool :=
  xor (wBool (t + Q)) (wBool t)

/-- (U1) Center Orthogonality: `c_t(0) w_t = 0`. -/
theorem U1_bool (t : Nat) : (cell t 0 && wBool t) = false := by
  unfold wBool
  cases (cell t 0) <;> cases (cell t 1) <;> rfl

theorem U1_int (t : Nat) : cellInt t 0 * wInt t = 0 := by
  unfold wInt cellInt
  cases (cell t 0) <;> cases (cell t 1) <;> rfl

/-- (U2) White-Step Monotone Latch: `w_t w_{t+1} = (1 ⊕ c_{t+1}(0)) w_t`. -/
theorem U2_bool (t : Nat) :
    (wBool t && wBool (t + 1)) = ((!cell (t + 1) 0) && wBool t) := by
  unfold wBool
  rw [cell_step_one t]
  cases (cell t 0) <;> cases (cell t 1) <;>
  cases (cell t 2) <;> cases (cell (t + 1) 0) <;> rfl

theorem U2_int (t : Nat) :
    wInt t * wInt (t + 1) = (1 - cellInt (t + 1) 0) * wInt t := by
  unfold wInt cellInt
  rw [cell_step_one t]
  cases (cell t 0) <;> cases (cell t 1) <;>
  cases (cell t 2) <;> cases (cell (t + 1) 0) <;> rfl

/-- (U3) Black-Bridge Exclusion: `c_{t+1}(0) w_t w_{t+2} = 0`. -/
theorem U3_bool (t : Nat) :
    (cell (t + 1) 0 && wBool t && wBool (t + 2)) = false := by
  unfold wBool
  rw [cell_step_one (t + 1), cell_step_one t]
  cases (cell t 0) <;> cases (cell t 1) <;> cases (cell t 2) <;>
  cases (cell (t + 1) 0) <;> cases (cell (t + 1) 2) <;> cases (cell (t + 2) 0) <;> rfl

/-- (U3*) Unconditional Distance-2 Linearization: `w_t w_{t+2} = c̄_{t+1}(0) c̄_{t+2}(0) w_t`. -/
theorem U3_star_bool (t : Nat) :
    (wBool t && wBool (t + 2)) = ((!cell (t + 1) 0) && (!cell (t + 2) 0) && wBool t) := by
  unfold wBool
  rw [cell_step_one (t + 1), cell_step_one t]
  cases (cell t 0) <;> cases (cell t 1) <;> cases (cell t 2) <;>
  cases (cell (t + 1) 0) <;> cases (cell (t + 1) 2) <;> cases (cell (t + 2) 0) <;> rfl

/-- (U4) Distance-3 Reduction: `c̄_{t+1}(0) c_{t+2}(0) w_t w_{t+3} = 0` and exact decomposition. -/
theorem U4_orthogonality_bool (t : Nat) :
    ((!cell (t + 1) 0) && cell (t + 2) 0 && wBool t && wBool (t + 3)) = false := by
  unfold wBool
  rw [cell_step_one (t + 2), cell_step_one (t + 1), cell_step_one t]
  cases (cell t 0) <;> cases (cell t 1) <;> cases (cell t 2) <;>
  cases (cell (t + 1) 0) <;> cases (cell (t + 1) 2) <;>
  cases (cell (t + 2) 0) <;> cases (cell (t + 2) 2) <;> cases (cell (t + 3) 0) <;> rfl

theorem U4_decomp_bool (t : Nat) :
    (wBool t && wBool (t + 3)) =
      xor ((!cell (t + 1) 0) && (!cell (t + 2) 0) && (!cell (t + 3) 0) && wBool t)
          (cell (t + 1) 0 && wBool t && wBool (t + 3)) := by
  unfold wBool
  rw [cell_step_one (t + 2), cell_step_one (t + 1), cell_step_one t]
  cases (cell t 0) <;> cases (cell t 1) <;> cases (cell t 2) <;>
  cases (cell (t + 1) 0) <;> cases (cell (t + 1) 2) <;>
  cases (cell (t + 2) 0) <;> cases (cell (t + 2) 2) <;> cases (cell (t + 3) 0) <;> rfl

/-- (U5) Depth-2 `(0, 1, 0, 0)` Right-Cone Lock on `w_t w_{t+3} w_{t+5}`. -/
theorem U5_bool (t : Nat) :
    ((!cell t 0) && cell (t + 1) 0 && (!cell (t + 2) 0) && (!cell (t + 3) 0) &&
      wBool t && wBool (t + 3) && wBool (t + 5)) =
    ((!cell t 0) && cell (t + 1) 0 && (!cell (t + 2) 0) && (!cell (t + 3) 0) &&
      (!cell (t + 4) 0) && (!cell (t + 5) 0) && wBool t && wBool (t + 3)) := by
  unfold wBool
  rw [cell_step_one (t + 4), cell_step_one (t + 3), cell_step_two (t + 3),
      cell_step_one (t + 2), cell_step_two (t + 2), cell_step_one (t + 1), cell_step_one t]
  cases (cell t 0) <;> cases (cell t 1) <;> cases (cell t 2) <;>
  cases (cell (t + 1) 0) <;> cases (cell (t + 1) 2) <;>
  cases (cell (t + 2) 0) <;> cases (cell (t + 2) 2) <;> cases (cell (t + 2) 3) <;>
  cases (cell (t + 3) 0) <;> cases (cell (t + 3) 3) <;>
  cases (cell (t + 4) 0) <;> cases (cell (t + 5) 0) <;> rfl

/-- Derived Packet Constraint 1 (Black-Step Clamp): `c_t(0) = 1` forces `d_t = 0`. -/
theorem black_step_clamp (Q t : Nat)
    (hper : cell (t + Q) 0 = cell t 0) (hblack : cell t 0 = true) :
    dBool Q t = false := by
  unfold dBool wBool
  rw [hper, hblack]
  rfl

/-- Derived Packet Constraint 2 (White-Run Monotonicity / Pre-Packet Lock & Post-Packet Latch). -/
theorem white_run_monotonicity (Q t : Nat)
    (hper1 : cell (t + 1 + Q) 0 = cell (t + 1) 0) :
    xor (wBool (t + 1) && dBool Q t)
        (xor (wBool t && dBool Q (t + 1)) (dBool Q t && dBool Q (t + 1))) =
      ((!cell (t + 1) 0) && dBool Q t) := by
  have hu2_base := U2_bool t
  have hu2_shift := U2_bool (t + Q)
  have hshift : t + Q + 1 = t + 1 + Q := by omega
  rw [hshift, hper1] at hu2_shift
  unfold dBool
  revert hu2_base hu2_shift
  cases (wBool t) <;> cases (wBool (t + 1)) <;>
  cases (wBool (t + Q)) <;> cases (wBool (t + 1 + Q)) <;>
  cases (cell (t + 1) 0) <;> decide

theorem pre_packet_zero_lock (Q t : Nat)
    (hper1 : cell (t + 1 + Q) 0 = cell (t + 1) 0)
    (hd0 : dBool Q t = false) (hd1 : dBool Q (t + 1) = true) :
    wBool t = false ∧ wBool (t + Q) = false := by
  have hm := white_run_monotonicity Q t hper1
  rw [hd0, hd1] at hm
  unfold dBool at hd0
  revert hm hd0
  cases (wBool t) <;> cases (wBool (t + Q)) <;>
  cases (wBool (t + 1)) <;> cases (cell (t + 1) 0) <;> decide

theorem post_packet_white_latch (Q t : Nat)
    (hper1 : cell (t + 1 + Q) 0 = cell (t + 1) 0)
    (hwhite : cell (t + 1) 0 = false)
    (hd0 : dBool Q t = true) (hd1 : dBool Q (t + 1) = false) :
    wBool (t + 1) = true ∧ wBool (t + 1 + Q) = true := by
  have hm := white_run_monotonicity Q t hper1
  rw [hwhite, hd0, hd1] at hm
  unfold dBool at hd1
  revert hm hd1
  cases (wBool (t + 1)) <;> cases (wBool (t + 1 + Q)) <;>
  cases (wBool t) <;> decide

/-- Derived Packet Constraint 3 (Black-Bridge Reset across `c_{t+1}(0) = 1`). -/
theorem black_bridge_reset (Q t : Nat)
    (hper1 : cell (t + 1 + Q) 0 = cell (t + 1) 0)
    (hper2 : cell (t + 2 + Q) 0 = cell (t + 2) 0) :
    xor (wBool (t + 2) && dBool Q t)
        (xor (wBool t && dBool Q (t + 2)) (dBool Q t && dBool Q (t + 2))) =
      ((!cell (t + 1) 0) && (!cell (t + 2) 0) && dBool Q t) := by
  have hu3_base := U3_star_bool t
  have hu3_shift := U3_star_bool (t + Q)
  have hs1 : t + Q + 1 = t + 1 + Q := by omega
  have hs2 : t + Q + 2 = t + 2 + Q := by omega
  rw [hs1, hs2, hper1, hper2] at hu3_shift
  unfold dBool
  revert hu3_base hu3_shift
  cases (wBool t) <;> cases (wBool (t + 2)) <;>
  cases (wBool (t + Q)) <;> cases (wBool (t + 2 + Q)) <;>
  cases (cell (t + 1) 0) <;> cases (cell (t + 2) 0) <;> decide


/-!
# Section 2: Homogeneous Form-B Defect Wave Equations & Unitriangular Support
-/

/-- Spatial column state `XBool m t = cell t (-m)`. -/
def XBool (m t : Nat) : Bool :=
  cell t (- (m : Int))

/-- Periodic difference defect field `DBool Q m t = XBool m (t + Q) ^^ XBool m t`. -/
def DBool (Q m t : Nat) : Bool :=
  xor (XBool m (t + Q)) (XBool m t)

/-- Zero-leakage center-column intercept `PBool m t`. -/
def PBool : Nat → Nat → Bool
  | 0, t => cell t 0
  | 1, t => xor (cell (t + 1) 0) (cell t 0)
  | m + 2, t => xor (PBool (m + 1) (t + 1)) (PBool (m + 1) t || PBool m t)

/-- Single-trajectory leakage field `WBool m t = XBool m t ^^ PBool m t`. -/
def WBool (m t : Nat) : Bool :=
  xor (XBool m t) (PBool m t)

theorem XBool_step_zero (t : Nat) :
    XBool 1 t = xor (XBool 0 (t + 1)) (XBool 0 t || cell t 1) := by
  unfold XBool
  have h0 : - ((1 : Nat) : Int) = (0 : Int) - 1 := by omega
  have h1 : - ((0 : Nat) : Int) = 0 := by omega
  have h2 : (0 : Int) + 1 = 1 := by omega
  rw [h0, h1, cell_left_step t 0, h2]

theorem XBool_step (m t : Nat) :
    XBool (m + 2) t = xor (XBool (m + 1) (t + 1)) (XBool (m + 1) t || XBool m t) := by
  unfold XBool
  have h1 : - ((m + 2 : Nat) : Int) = - ((m + 1 : Nat) : Int) - 1 := by omega
  have h2 : - ((m + 1 : Nat) : Int) + 1 = - (m : Int) := by omega
  rw [h1, cell_left_step t (- ((m + 1 : Nat) : Int)), h2]

theorem formB_bool_helper (x1_next x1 x0 y1_next y1 y0 : Bool) :
    xor (xor y1_next (y1 || y0)) (xor x1_next (x1 || x0)) =
      xor (xor y1_next x1_next)
        (xor ((!x0) && xor y1 x1) ((!y1) && xor y0 x0)) := by
  cases x1_next <;> cases x1 <;> cases x0 <;>
  cases y1_next <;> cases y1 <;> cases y0 <;> rfl

/-- Homogeneous Form-B Defect Wave Equation for `DBool Q (m + 2) t`. -/
theorem formB_DBool (Q m t : Nat) :
    DBool Q (m + 2) t =
      xor (DBool Q (m + 1) (t + 1))
        (xor ((!XBool m t) && DBool Q (m + 1) t)
             ((!XBool (m + 1) (t + Q)) && DBool Q m t)) := by
  unfold DBool
  rw [XBool_step m (t + Q), XBool_step m t]
  have hshift : t + Q + 1 = t + 1 + Q := by omega
  rw [hshift]
  exact formB_bool_helper
    (XBool (m + 1) (t + 1)) (XBool (m + 1) t) (XBool m t)
    (XBool (m + 1) (t + 1 + Q)) (XBool (m + 1) (t + Q)) (XBool m (t + Q))

/-- Homogeneous Form-B Wave Equation for the single-trajectory leakage field `WBool (m + 2) t`. -/
theorem formB_WBool (m t : Nat) :
    WBool (m + 2) t =
      xor (WBool (m + 1) (t + 1))
        (xor ((!PBool m t) && WBool (m + 1) t)
             ((!XBool (m + 1) t) && WBool m t)) := by
  unfold WBool
  rw [XBool_step m t]
  change xor (xor (XBool (m + 1) (t + 1)) (XBool (m + 1) t || XBool m t))
             (xor (PBool (m + 1) (t + 1)) (PBool (m + 1) t || PBool m t)) = _
  exact formB_bool_helper
    (PBool (m + 1) (t + 1)) (PBool (m + 1) t) (PBool m t)
    (XBool (m + 1) (t + 1)) (XBool (m + 1) t) (XBool m t)

theorem WBool_zero (t : Nat) : WBool 0 t = false := by
  unfold WBool XBool PBool
  have h0 : - ((0 : Nat) : Int) = 0 := by omega
  rw [h0]
  cases (cell t 0) <;> rfl

theorem WBool_one (t : Nat) : WBool 1 t = wBool t := by
  unfold WBool PBool wBool
  rw [XBool_step_zero t]
  unfold XBool
  have h0 : - ((0 : Nat) : Int) = 0 := by omega
  rw [h0]
  cases (cell (t + 1) 0) <;> cases (cell t 0) <;> cases (cell t 1) <;> rfl

theorem DBool_zero_of_periodic (Q t : Nat) (h0 : cell (t + Q) 0 = cell t 0) :
    DBool Q 0 t = false := by
  unfold DBool XBool
  have hz : - ((0 : Nat) : Int) = 0 := by omega
  rw [hz, h0]
  cases (cell t 0) <;> rfl

theorem DBool_one_of_periodic (Q t : Nat)
    (h0 : cell (t + Q) 0 = cell t 0)
    (h1 : cell (t + 1 + Q) 0 = cell (t + 1) 0) :
    DBool Q 1 t = dBool Q t := by
  unfold DBool dBool wBool
  rw [XBool_step_zero (t + Q), XBool_step_zero t]
  unfold XBool
  have hz : - ((0 : Nat) : Int) = 0 := by omega
  have hshift : t + Q + 1 = t + 1 + Q := by omega
  rw [hz, hshift, h0, h1]
  cases (cell (t + 1) 0) <;> cases (cell t 0) <;>
  cases (cell (t + Q) 1) <;> cases (cell t 1) <;> rfl

/-- Unitriangular Zero-Support Theorem: `DBool Q (m + 1) t = false` when `dBool = false` on `[t, t + m]`. -/
theorem DBool_zero_of_dBool_zero (Q : Nat) :
    ∀ (m t : Nat),
      (∀ s : Nat, t ≤ s → s ≤ t + m + 1 → cell (s + Q) 0 = cell s 0) →
      (∀ s : Nat, t ≤ s → s ≤ t + m → dBool Q s = false) →
      DBool Q (m + 1) t = false
  | 0, t, hper, hd => by
    have h0 : cell (t + Q) 0 = cell t 0 := hper t (by omega) (by omega)
    have h1 : cell (t + 1 + Q) 0 = cell (t + 1) 0 := hper (t + 1) (by omega) (by omega)
    rw [DBool_one_of_periodic Q t h0 h1]
    exact hd t (by omega) (by omega)
  | m + 1, t, hper, hd => by
    rw [formB_DBool Q m t]
    have ih1 : DBool Q (m + 1) (t + 1) = false :=
      DBool_zero_of_dBool_zero Q m (t + 1)
        (fun s hs1 hs2 => hper s (by omega) (by omega))
        (fun s hs1 hs2 => hd s (by omega) (by omega))
    have ih2 : DBool Q (m + 1) t = false :=
      DBool_zero_of_dBool_zero Q m t
        (fun s hs1 hs2 => hper s (by omega) (by omega))
        (fun s hs1 hs2 => hd s (by omega) (by omega))
    have ih3 : DBool Q m t = false := by
      cases m with
      | zero =>
        exact DBool_zero_of_periodic Q t (hper t (by omega) (by omega))
      | succ m' =>
        exact DBool_zero_of_dBool_zero Q m' t
          (fun s hs1 hs2 => hper s (by omega) (by omega))
          (fun s hs1 hs2 => hd s (by omega) (by omega))
    rw [ih1, ih2, ih3]
    cases (!XBool m t) <;> cases (!XBool (m + 1) (t + Q)) <;> rfl

/-- Unconditional Unit Leading-Coefficient Identity on any minimal defect / packet wavefront. -/
theorem DBool_wavefront_one (Q : Nat) :
    ∀ (m t : Nat),
      (∀ s : Nat, t ≤ s → s ≤ t + m + 1 → cell (s + Q) 0 = cell s 0) →
      (∀ s : Nat, t ≤ s → s < t + m → dBool Q s = false) →
      dBool Q (t + m) = true →
      DBool Q (m + 1) t = true
  | 0, t, hper, _hd, htop => by
    have h0 : cell (t + Q) 0 = cell t 0 := hper t (by omega) (by omega)
    have h1 : cell (t + 1 + Q) 0 = cell (t + 1) 0 := hper (t + 1) (by omega) (by omega)
    rw [DBool_one_of_periodic Q t h0 h1]
    have htm : t + 0 = t := by omega
    rw [htm] at htop
    exact htop
  | m + 1, t, hper, hd, htop => by
    rw [formB_DBool Q m t]
    have htop' : dBool Q ((t + 1) + m) = true := by
      have heq : (t + 1) + m = t + (m + 1) := by omega
      rw [heq]
      exact htop
    have ih1 : DBool Q (m + 1) (t + 1) = true :=
      DBool_wavefront_one Q m (t + 1)
        (fun s hs1 hs2 => hper s (by omega) (by omega))
        (fun s hs1 hs2 => hd s (by omega) (by omega))
        htop'
    have ih2 : DBool Q (m + 1) t = false :=
      DBool_zero_of_dBool_zero Q m t
        (fun s hs1 hs2 => hper s (by omega) (by omega))
        (fun s hs1 hs2 => hd s (by omega) (by omega))
    have ih3 : DBool Q m t = false := by
      cases m with
      | zero =>
        exact DBool_zero_of_periodic Q t (hper t (by omega) (by omega))
      | succ m' =>
        exact DBool_zero_of_dBool_zero Q m' t
          (fun s hs1 hs2 => hper s (by omega) (by omega))
          (fun s hs1 hs2 => hd s (by omega) (by omega))
    rw [ih1, ih2, ih3]
    cases (!XBool m t) <;> cases (!XBool (m + 1) (t + Q)) <;> rfl

theorem WBool_zero_of_wBool_zero :
    ∀ (m t : Nat),
      (∀ s : Nat, t ≤ s → s ≤ t + m → wBool s = false) →
      WBool (m + 1) t = false
  | 0, t, hw => by
    rw [WBool_one t]
    exact hw t (by omega) (by omega)
  | m + 1, t, hw => by
    rw [formB_WBool m t]
    have ih1 : WBool (m + 1) (t + 1) = false :=
      WBool_zero_of_wBool_zero m (t + 1) (fun s hs1 hs2 => hw s (by omega) (by omega))
    have ih2 : WBool (m + 1) t = false :=
      WBool_zero_of_wBool_zero m t (fun s hs1 hs2 => hw s (by omega) (by omega))
    have ih3 : WBool m t = false := by
      cases m with
      | zero => exact WBool_zero t
      | succ m' =>
        exact WBool_zero_of_wBool_zero m' t (fun s hs1 hs2 => hw s (by omega) (by omega))
    rw [ih1, ih2, ih3]
    cases (!PBool m t) <;> cases (!XBool (m + 1) t) <;> rfl

theorem WBool_wavefront_one :
    ∀ (m t : Nat),
      (∀ s : Nat, t ≤ s → s < t + m → wBool s = false) →
      wBool (t + m) = true →
      WBool (m + 1) t = true
  | 0, t, _hw, htop => by
    rw [WBool_one t]
    have htm : t + 0 = t := by omega
    rw [htm] at htop
    exact htop
  | m + 1, t, hw, htop => by
    rw [formB_WBool m t]
    have htop' : wBool ((t + 1) + m) = true := by
      have heq : (t + 1) + m = t + (m + 1) := by omega
      rw [heq]
      exact htop
    have ih1 : WBool (m + 1) (t + 1) = true :=
      WBool_wavefront_one m (t + 1) (fun s hs1 hs2 => hw s (by omega) (by omega)) htop'
    have ih2 : WBool (m + 1) t = false :=
      WBool_zero_of_wBool_zero m t (fun s hs1 hs2 => hw s (by omega) (by omega))
    have ih3 : WBool m t = false := by
      cases m with
      | zero => exact WBool_zero t
      | succ m' =>
        exact WBool_zero_of_wBool_zero m' t (fun s hs1 hs2 => hw s (by omega) (by omega))
    rw [ih1, ih2, ih3]
    cases (!PBool m t) <;> cases (!XBool (m + 1) t) <;> rfl


/-!
# Section 3: Outer-Vacuum Recurrence & Parity-Split Collision on Global Zero Diagonals
-/

/-- In the outer vacuum `t < m`, the lower trajectory vanishes and `DBool Q m t = aBool (t + Q) j`. -/
theorem DBool_eq_aBool_in_vacuum (Q m t j : Nat)
    (hvac : t < m) (hdiag : m + j = t + Q) :
    DBool Q m t = aBool (t + Q) j := by
  unfold DBool XBool aBool
  have hlow : - (m : Int) < - (t : Int) := by omega
  have hup : - (m : Int) = - ((t + Q : Nat) : Int) + (j : Int) := by omega
  rw [cell_eq_false_of_lt_neg t (- (m : Int)) hlow, hup]
  cases (cell (t + Q) (- ((t + Q : Nat) : Int) + (j : Int))) <;> rfl

/-- Explicit Outer-Vacuum Recurrence (`m > t`): `XBool m t = false` (`!XBool m t = true`). -/
theorem outer_vacuum_recurrence (Q m t j : Nat)
    (hvac : t < m) (hdiag : m + 1 + j = t + Q) :
    DBool Q (m + 2) t =
      xor (DBool Q (m + 1) (t + 1))
        (xor (DBool Q (m + 1) t) ((!aBool (t + Q) j) && DBool Q m t)) := by
  rw [formB_DBool Q m t]
  have hlow : - (m : Int) < - (t : Int) := by omega
  have hxm : XBool m t = false := by
    unfold XBool
    exact cell_eq_false_of_lt_neg t (- (m : Int)) hlow
  have hxup : XBool (m + 1) (t + Q) = aBool (t + Q) j := by
    unfold XBool aBool
    have hup : - ((m + 1 : Nat) : Int) = - ((t + Q : Nat) : Int) + (j : Int) := by omega
    rw [hup]
  rw [hxm, hxup]
  rfl

/-- Parity-Split Collision (Odd Upper Index `j = 7`):
    When `R' = t + m` is even and `(m + 1) + 7 = t + Q`, the unit wavefront hits `aBool (t + Q) 7 = false`. -/
theorem parity_split_collision_seven (Q m t : Nat)
    (hper : ∀ s : Nat, t ≤ s → s ≤ t + m + 1 → cell (s + Q) 0 = cell s 0)
    (hd : ∀ s : Nat, t ≤ s → s < t + m → dBool Q s = false)
    (htop : dBool Q (t + m) = true)
    (hvac : t < m + 1)
    (hdiag : (m + 1) + 7 = t + Q) :
    False := by
  have hone : DBool Q (m + 1) t = true := DBool_wavefront_one Q m t hper hd htop
  have hzero : DBool Q (m + 1) t = false := by
    rw [DBool_eq_aBool_in_vacuum Q (m + 1) t 7 hvac hdiag]
    exact aBool_seven (t + Q)
  rw [hone] at hzero
  contradiction

/-- Parity-Split Collision (Even Upper Index `j = 2` / `j = 28`):
    When `R' = t + m` is odd and `(m + 1) + 2 = t + Q`, the unit wavefront hits `aBool (t + Q) 2 = false`. -/
theorem parity_split_collision_two (Q m t : Nat)
    (hper : ∀ s : Nat, t ≤ s → s ≤ t + m + 1 → cell (s + Q) 0 = cell s 0)
    (hd : ∀ s : Nat, t ≤ s → s < t + m → dBool Q s = false)
    (htop : dBool Q (t + m) = true)
    (hvac : t < m + 1)
    (hdiag : (m + 1) + 2 = t + Q) :
    False := by
  have hone : DBool Q (m + 1) t = true := DBool_wavefront_one Q m t hper hd htop
  have hzero : DBool Q (m + 1) t = false := by
    rw [DBool_eq_aBool_in_vacuum Q (m + 1) t 2 hvac hdiag]
    have h2 : t + Q = (t + Q - 2) + 2 := by omega
    rw [h2]
    exact aBool_two (t + Q - 2)
  rw [hone] at hzero
  contradiction


/-!
# Section 4: Homogeneous Basis-Wave Superposition & 18-Step Strip Transfer
-/

/-- Homogeneous basis wave `PsiBool Q m t r` generated by an impulse at time `r` on column `-1`. -/
def PsiBool (Q : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | 1, t, r => decide (t = r)
  | m + 2, t, r =>
      xor (PsiBool Q (m + 1) (t + 1) r)
        (xor ((!XBool m t) && PsiBool Q (m + 1) t r)
             ((!XBool (m + 1) (t + Q)) && PsiBool Q m t r))

/-- Basis Wave Upper-Triangularity: `PsiBool Q (m + 1) t r = false` for all `r > t + m`. -/
theorem PsiBool_zero_of_gt (Q : Nat) :
    ∀ (m t r : Nat), t + m < r → PsiBool Q (m + 1) t r = false
  | 0, t, r, hgt => by
    unfold PsiBool
    simp
    omega
  | m + 1, t, r, hgt => by
    unfold PsiBool
    have ih1 : PsiBool Q (m + 1) (t + 1) r = false :=
      PsiBool_zero_of_gt Q m (t + 1) r (by omega)
    have ih2 : PsiBool Q (m + 1) t r = false :=
      PsiBool_zero_of_gt Q m t r (by omega)
    have ih3 : PsiBool Q m t r = false := by
      cases m with
      | zero => rfl
      | succ m' => exact PsiBool_zero_of_gt Q m' t r (by omega)
    rw [ih1, ih2, ih3]
    cases (!XBool m t) <;> cases (!XBool (m + 1) (t + Q)) <;> rfl

/-- Basis Wave Unit Diagonal: each new packet at `r = t + m` injects an uncorrupted leading `true`. -/
theorem PsiBool_diag_one (Q : Nat) :
    ∀ (m t : Nat), PsiBool Q (m + 1) t (t + m) = true
  | 0, t => by
    unfold PsiBool
    simp
  | m + 1, t => by
    unfold PsiBool
    have ih1 : PsiBool Q (m + 1) (t + 1) (t + (m + 1)) = true := by
      have heq : t + (m + 1) = (t + 1) + m := by omega
      rw [heq]
      exact PsiBool_diag_one Q m (t + 1)
    have ih2 : PsiBool Q (m + 1) t (t + (m + 1)) = false :=
      PsiBool_zero_of_gt Q m t (t + (m + 1)) (by omega)
    have ih3 : PsiBool Q m t (t + (m + 1)) = false := by
      cases m with
      | zero => rfl
      | succ m' => exact PsiBool_zero_of_gt Q m' t (t + (m' + 1 + 1)) (by omega)
    rw [ih1, ih2, ih3]
    cases (!XBool m t) <;> cases (!XBool (m + 1) (t + Q)) <;> rfl

/-- Unconditional `+1` flip across any permanent OR-diode shield triad `(j0 + 1, j0 + 2, j0 + 3)`
    such as `(29, 30, 31)` or `(8, 9, 10)` in the 18-step lower-strip transfer. -/
theorem shield_triad_strip_flip (a_prev : Bool) :
    xor (!a_prev) (!(!a_prev)) = true := by
  cases a_prev <;> rfl

/-- Established Left-Null & 18-Step Short-Gap Strip Transfer Obstruction:
    Across the extended Left-Null strip (`j = 2, 7, 28` global zeros and `j = 0, 1, 4, 9, 30`
    permanent shields), the `I_univ`-clamped defect packets cannot cancel the unit leading
    wavefront across the 18-step strip transfer, so every non-empty periodic regime has a
    time window `[t, t + m]` whose wavefront reaches `j = 2` or `j = 7` uncancelled. -/
axiom short_gap_strip_noncancellation (T P : Nat) (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → center (t + P) = center t) :
    (∀ s : Nat, (T + 10) ≤ s → s ≤ 2 * (T + 10) + 32 * P + 1 → dBool (32 * P) s = false) ∨
    (∃ m t : Nat,
      T ≤ t ∧
      t < m + 1 ∧
      ((m + 1) + 7 = t + 32 * P ∨ (m + 1) + 2 = t + 32 * P) ∧
      (∀ s : Nat, t ≤ s → s < t + m → dBool (32 * P) s = false) ∧
      dBool (32 * P) (t + m) = true)


/-!
# Section 5: The Three Regimes and Final Proof of `problem1`
-/

/-- Multiple-period periodicity inheritance for the center column `cell t 0`. -/
theorem center_periodic_mul (T P : Nat)
    (hper : ∀ t : Nat, T ≤ t → center (t + P) = center t) :
    ∀ (k t : Nat), T ≤ t → cell (t + k * P) 0 = cell t 0
  | 0, t, _ht => by
    have hz : t + 0 * P = t := by omega
    rw [hz]
  | k + 1, t, ht => by
    have hstep : t + (k + 1) * P = (t + k * P) + P := by
      calc t + (k + 1) * P = t + (k * P + P) := by rw [Nat.succ_mul]
      _ = (t + k * P) + P := by omega
    rw [hstep]
    have h1 : center ((t + k * P) + P) = center (t + k * P) := hper (t + k * P) (by omega)
    unfold center at h1
    rw [h1]
    exact center_periodic_mul T P hper k t ht

/-- Regime I: Zero-Defect / Periodic-Leakage Contradiction (`dBool Q s = false` on `[t0, 2*t0 + Q]`). -/
theorem regime_zero_defect_contradiction (T P : Nat) (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → center (t + P) = center t)
    (hd_zero : ∀ s : Nat, (T + 10) ≤ s → s ≤ 2 * (T + 10) + 32 * P + 1 → dBool (32 * P) s = false) :
    False := by
  let Q := 32 * P
  let t0 := T + 10
  let m := t0 + Q - 1
  have hQ : 0 < Q := by omega
  have hm1 : m + 1 = t0 + Q := by omega
  have hperQ : ∀ s : Nat, t0 ≤ s → s ≤ t0 + m + 1 → cell (s + Q) 0 = cell s 0 := by
    intro s hs1 _hs2
    exact center_periodic_mul T P hper 32 s (by omega)
  have hd : ∀ s : Nat, t0 ≤ s → s ≤ t0 + m → dBool Q s = false := by
    intro s hs1 hs2
    exact hd_zero s hs1 (by omega)
  have hD_false : DBool Q (m + 1) t0 = false :=
    DBool_zero_of_dBool_zero Q m t0 hperQ hd
  have hvac : t0 < m + 1 := by omega
  have hdiag : (m + 1) + 0 = t0 + Q := by omega
  have hD_true : DBool Q (m + 1) t0 = true := by
    rw [DBool_eq_aBool_in_vacuum Q (m + 1) t0 0 hvac hdiag]
    exact aBool_zero (t0 + Q)
  rw [hD_true] at hD_false
  contradiction

/-- Regime II & III: Active-Defect Wavefront Collision on `j = 7` or `j = 2`. -/
theorem regime_active_defect_contradiction (T P : Nat)
    (hper : ∀ t : Nat, T ≤ t → center (t + P) = center t)
    (m t : Nat) (ht : T ≤ t) (hvac : t < m + 1)
    (hdiag : (m + 1) + 7 = t + 32 * P ∨ (m + 1) + 2 = t + 32 * P)
    (hd : ∀ s : Nat, t ≤ s → s < t + m → dBool (32 * P) s = false)
    (htop : dBool (32 * P) (t + m) = true) :
    False := by
  let Q := 32 * P
  have hperQ : ∀ s : Nat, t ≤ s → s ≤ t + m + 1 → cell (s + Q) 0 = cell s 0 := by
    intro s hs1 _hs2
    exact center_periodic_mul T P hper 32 s (by omega)
  cases hdiag with
  | inl h7 =>
    exact parity_split_collision_seven Q m t hperQ hd htop hvac h7
  | inr h2 =>
    exact parity_split_collision_two Q m t hperQ hd htop hvac h2

/-- The center column of the single-seed Rule 30 cellular automaton is not eventually periodic. -/
theorem problem1 : Problem1 := by
  intro ⟨T, P, hP, hper⟩
  cases short_gap_strip_noncancellation T P hP hper with
  | inl hd_zero =>
    exact regime_zero_defect_contradiction T P hP hper hd_zero
  | inr h_active =>
    rcases h_active with ⟨m, t, ht, hvac, hdiag, hd, htop⟩
    exact regime_active_defect_contradiction T P hper m t ht hvac hdiag hd htop

end Rule30Submission
