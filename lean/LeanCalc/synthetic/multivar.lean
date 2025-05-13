
import Mathlib.Order.Monotone.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
open Real
open Set

example (x y : ℝ) : (fderiv ℝ (fun p ↦ p.1 ^ 2 + p.1 + p.2 ^ 2 - 25) (x-3, y-4) (3, 4) = 0) → ((3:ℝ) * ((2:ℝ) * (x - (3:ℝ)) + (1:ℝ)) + (4:ℝ) * ((2:ℝ) * (y - (4:ℝ))) = 0) := by
  intro h
  rw [fderiv_sub, fderiv_add] at h
  simp at h

  have h1 : fderiv ℝ (fun p : ℝ × ℝ => p.1 ^ 2 + p.1) (x-3, y-4) (3, 4) = (3:ℝ) * ((2:ℝ) * (x - (3:ℝ)) + (1:ℝ)) := by
    have hp1comp : (fun p : ℝ × ℝ => p.1 ^ 2 + p.1) = (fun x => x ^ 2 + x) ∘ (fun p => p.1) := rfl
    rw [hp1comp]
    rw [fderiv_comp]
    simp [fderiv_fst]
    ring
    exact DifferentiableAt () (differentiableAt_fst.pow _)
    exact differentiableAt_pow _
    exact differentiableAt_fst

  have h2 : fderiv ℝ (fun p : ℝ × ℝ => p.2 ^ 2) (x-3, y-4) (3, 4) = (4:ℝ) * ((2:ℝ) * (y - (4:ℝ)))  := by
    have hp2comp : (fun p : ℝ × ℝ => p.2 ^ 2) = (fun y => y ^ 2) ∘ (fun p => p.2) := rfl
    rw [hp2comp]
    rw [fderiv_comp]
    simp [fderiv_snd]
    ring
    exact differentiableAt_pow _
    exact differentiableAt_snd

  rw [h1] at h
  rw [h2] at h
  ring_nf at h
  linarith
  exact differentiableAt_fst.pow _
  exact differentiableAt_snd.pow _
  exact DifferentiableAt.add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)
  exact differentiableAt_const _
