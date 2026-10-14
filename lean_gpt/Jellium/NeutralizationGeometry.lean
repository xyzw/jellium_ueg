import Jellium.Domains
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

/-! Explicit integer rounding and shell geometry for canonical completion.
All radii, particle counts and uniform constants are constructed here. -/

namespace Jellium.NeutralizationGeometry

open Domains

noncomputable def ballFactor : ℝ := Real.pi * 4 / 3

theorem ballFactor_pos : 0 < ballFactor := by unfold ballFactor; positivity

structure PreparedAnnulus (ρ R H L : ℝ) (N : ℕ) where
  radius : ℝ
  total : ℕ
  particles : ℕ
  radius_lower : R + 4 ≤ radius
  radius_upper : radius ≤ R + H
  neutral : ρ * ballVolume radius = (total : ℝ)
  count : particles + N = total
  particles_pos : 0 < particles
  particles_le : (particles : ℝ) ≤ L * R ^ 2
  background_nonnegative : 0 ≤ ρ * (ballVolume radius - ballVolume R)
  background_le : ρ * (ballVolume radius - ballVolume R) ≤ L * R ^ 2
  trimmed_lower : 8 * Real.pi * R ^ 2 ≤ ballVolume (radius - 1) - ballVolume (R + 1)
  sampling_bound : (particles : ℝ) /
    (ballVolume (radius - 1) - ballVolume (R + 1)) ≤ L / (8 * Real.pi)

theorem cube_increment_lower (R h : ℝ) (hR : 0 ≤ R) (hh : 0 ≤ h) :
    h * R ^ 2 ≤ (R + h) ^ 3 - R ^ 3 := by
  nlinarith [mul_nonneg hh (sq_nonneg R), mul_nonneg hR (sq_nonneg h),
    pow_nonneg hh 3]

theorem cube_increment_upper (R h : ℝ) (hR : 1 ≤ R) (hh : 0 ≤ h) :
    (R + h) ^ 3 - R ^ 3 ≤ (3 * h + 3 * h ^ 2 + h ^ 3) * R ^ 2 := by
  have hR2 : R ≤ R ^ 2 := by nlinarith
  have h1 : 1 ≤ R ^ 2 := by nlinarith
  have h₂ := mul_le_mul_of_nonneg_left hR2 (by positivity : 0 ≤ 3 * h ^ 2)
  have h₃ := mul_le_mul_of_nonneg_left h1 (pow_nonneg hh 3)
  nlinarith

theorem exists_prepared_annulus {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K) :
    ∃ H L : ℝ, 0 < H ∧ 0 < L ∧ ∀ (R : ℝ) (N : ℕ), 1 ≤ R →
      |(N : ℝ) - ρ * ballVolume R| ≤ K * R ^ 2 →
      Nonempty (PreparedAnnulus ρ R H L N) := by
  let b := ρ * ballFactor
  have hb : 0 < b := mul_pos hρ ballFactor_pos
  let H₀ := 4 + (2 * K + 1) / b
  have hH₀ : 4 ≤ H₀ := by
    dsimp [H₀]
    have : 0 ≤ (2 * K + 1) / b := by positivity
    linarith only [this]
  have hH₀pos : 0 < H₀ := by linarith only [hH₀]
  have hgain : 2 * K + 1 ≤ b * H₀ := by
    dsimp [H₀]
    rw [mul_add, mul_div_cancel₀ _ hb.ne']
    nlinarith only [hb]
  let H := H₀ + 1
  have hH : 0 < H := by dsimp [H]; positivity
  let A := b * (3 * H + 3 * H ^ 2 + H ^ 3)
  let L := A + K + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨H, L, hH, hL, ?_⟩
  intro R N hR hQ
  have hRpos : 0 < R := by linarith only [hR]
  have hR2 : 1 ≤ R ^ 2 := by nlinarith only [hR]
  let M : ℕ := ⌈b * (R + H₀) ^ 3⌉₊
  have hMlo : b * (R + H₀) ^ 3 ≤ (M : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) < b * (R + H₀) ^ 3 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMlo
  let S : ℝ := ((M : ℝ) / b) ^ ((3 : ℝ)⁻¹)
  have hSpos : 0 < S := Real.rpow_pos_of_pos (div_pos hMpos hb) _
  have hScube : S ^ 3 = (M : ℝ) / b :=
    Real.rpow_inv_natCast_pow (div_nonneg hMpos.le hb.le) (by norm_num : (3 : ℕ) ≠ 0)
  have hneutral : b * S ^ 3 = (M : ℝ) := by rw [hScube]; field_simp
  have hSlo : R + H₀ ≤ S := by
    by_contra h
    have hp := pow_lt_pow_left₀ (lt_of_not_ge h) hSpos.le (by decide : 3 ≠ 0)
    have := mul_lt_mul_of_pos_left hp hb
    linarith only [hMlo, hneutral, this]
  have hRbase : H₀ ≤ (R + H₀) ^ 2 := by nlinarith only [hR, hH₀]
  have hstep := cube_increment_lower (R + H₀) 1 (by positivity) (by norm_num)
  have hstep' := mul_le_mul_of_nonneg_left hstep hb.le
  have hone := mul_le_mul_of_nonneg_left hRbase hb.le
  have htop : b * (R + H₀) ^ 3 + 1 ≤ b * (R + H) ^ 3 := by
    have hid : R + H₀ + 1 = R + H := by dsimp [H]; ring
    rw [hid] at hstep'
    nlinarith only [hstep', hone, hgain, hK]
  have hShi : S ≤ R + H := by
    by_contra h
    have hp := pow_lt_pow_left₀ (lt_of_not_ge h) (by positivity : 0 ≤ R + H)
      (by decide : 3 ≠ 0)
    have := mul_lt_mul_of_pos_left hp hb
    linarith only [this, hneutral, hMhi, htop]
  have hV : ∀ r : ℝ, ρ * ballVolume r = b * r ^ 3 := by
    intro r
    dsimp [ballVolume, b, ballFactor]
    ring
  have hmasslo : (2 * K + 1) * R ^ 2 ≤ (M : ℝ) - ρ * ballVolume R := by
    have hinc := cube_increment_lower R H₀ hRpos.le hH₀pos.le
    have hinc' := mul_le_mul_of_nonneg_left hinc hb.le
    have hgain' := mul_le_mul_of_nonneg_right hgain (sq_nonneg R)
    rw [hV]
    nlinarith only [hMlo, hinc', hgain']
  have hmasshi : (M : ℝ) - ρ * ballVolume R ≤ A * R ^ 2 := by
    have hinc := cube_increment_upper R H hR hH.le
    have hinc' := mul_le_mul_of_nonneg_left hinc hb.le
    have hp := pow_le_pow_left₀ hSpos.le hShi 3
    have hp' := mul_le_mul_of_nonneg_left hp hb.le
    rw [hV]
    dsimp [A]
    nlinarith only [hinc', hp', hneutral]
  have hN : (N : ℝ) < M := by
    have hu := (abs_le.mp hQ).2
    have hp := mul_nonneg hK (sq_nonneg R)
    nlinarith only [hu, hmasslo, hp, hR2]
  have hNM : N ≤ M := by exact_mod_cast hN.le
  let P := M - N
  have hcount : P + N = M := Nat.sub_add_cancel hNM
  have hPcast : (P : ℝ) = (M : ℝ) - N := by
    dsimp [P]
    exact Nat.cast_sub hNM
  have hPpos : 0 < P := by
    have : (0 : ℝ) < P := by rw [hPcast]; linarith only [hN]
    exact_mod_cast this
  have hPle : (P : ℝ) ≤ L * R ^ 2 := by
    have hl := (abs_le.mp hQ).1
    rw [hPcast]
    dsimp [L]
    nlinarith only [hmasshi, hl, sq_nonneg R]
  have hS4 : R + 4 ≤ S := by linarith only [hSlo, hH₀]
  have htrim : 8 * Real.pi * R ^ 2 ≤ ballVolume (S - 1) - ballVolume (R + 1) := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ R + 3)
      (by linarith only [hS4] : R + 3 ≤ S - 1) 3
    have hpoly : 6 * R ^ 2 ≤ (R + 3) ^ 3 - (R + 1) ^ 3 := by
      nlinarith only [hR]
    have hp' := mul_le_mul_of_nonneg_left hp ballFactor_pos.le
    have hpoly' := mul_le_mul_of_nonneg_left hpoly ballFactor_pos.le
    have hfactor : 8 * Real.pi = 6 * ballFactor := by unfold ballFactor; ring
    rw [hfactor]
    change 6 * ballFactor * R ^ 2 ≤ ballFactor * (S - 1) ^ 3 - ballFactor * (R + 1) ^ 3
    linarith only [hp', hpoly']
  have htrimpos : 0 < ballVolume (S - 1) - ballVolume (R + 1) :=
    lt_of_lt_of_le (by positivity) htrim
  refine ⟨⟨S, M, P, hS4, hShi, ?_, hcount, hPpos, hPle, ?_, ?_, htrim, ?_⟩⟩
  · rw [hV]
    exact hneutral
  · rw [mul_sub, hV S, hneutral, hV R]
    have := hmasslo
    rw [hV] at this
    nlinarith only [this, mul_nonneg (by positivity : 0 ≤ 2 * K + 1) (sq_nonneg R)]
  · rw [mul_sub, hV S, hneutral, hV R]
    rw [hV] at hmasshi
    dsimp [L]
    nlinarith only [hmasshi, mul_nonneg hK (sq_nonneg R), sq_nonneg R]
  · apply (div_le_iff₀ htrimpos).2
    have hprod := mul_le_mul_of_nonneg_left htrim
      (div_nonneg hL.le (by positivity : (0 : ℝ) ≤ 8 * Real.pi))
    have hid : (L / (8 * Real.pi)) * (8 * Real.pi * R ^ 2) = L * R ^ 2 := by
      field_simp
    rw [hid] at hprod
    exact le_trans hPle hprod

end Jellium.NeutralizationGeometry
