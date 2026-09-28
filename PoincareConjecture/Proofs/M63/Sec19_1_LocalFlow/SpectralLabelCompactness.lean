import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceLabelVelocityLp
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicLabelCompactness

set_option autoImplicit false

open Set Filter MeasureTheory AddCircle PoincareConjecture.SpectralHeatNative
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "H" => State ((ℤ × Fin 2) × ι)

theorem exists_compact_spectral_label_displacements
    (F : RicciFlow n M (Icc a b)) {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {S L : ℝ} (hS : 0 < S) (hSb : S < b - a) [Fact (0 < L)]
    {K : Set (W × W)} (hK : IsCompact K)
    (hKU : K ⊆ {z : W × W | z.1 ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (Vn : ℕ → C(Icc (0 : ℝ) S, H)) (V : C(Icc (0 : ℝ) S, H))
    (hV : Tendsto Vn atTop (𝓝 V)) (qn : ℕ → ℝ → ℝ → W)
    (hq : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (qn j)) (Icc 0 S ×ˢ univ))
    (hqzero : ∀ j (t : Icc (0 : ℝ) S) (x : ℝ), qn j t.1 x =
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega)
        (Vn j t) (x : AddCircle L)))
    (hphase : ∀ j (t : Icc (0 : ℝ) S), DifferentiableAt ℝ
      (fun r : ℝ => vectorPeriodicSpectralTranslation (L := L) r (Vn j t)) 0)
    (hjets : ∀ j (t : Icc (0 : ℝ) S) (x : AddCircle L),
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) (Vn j t) x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) (Vn j t) x)) ∈ K)
    (psi : ℕ → ℝ → ℝ → ℝ)
    (hpsi : ∀ j, ContDiffOn ℝ 1 (Function.uncurry (psi j)) (Icc 0 S ×ˢ univ))
    (hshift : ∀ j t, t ∈ Icc 0 S → ∀ x,
      psi j t (x + L) = psi j t x + L)
    (hinitial : ∀ j x, psi j 0 x = x)
    (htime : ∀ j t, t ∈ Ioo 0 S → ∀ x,
      HasDerivAt (fun r => psi j r x)
        (deriv (fun y => ambientCurvePrincipal F ρ (a + t)
          (qn j t y) (deriv (qn j t) y)) (psi j t x) / 2) t)
    {ell upper : ℝ} (hell : 0 < ell)
    (hlower : ∀ j t, t ∈ Icc 0 S → ∀ x, ell ≤ deriv (psi j t) x)
    (hupper : ∀ j t, t ∈ Icc 0 S → ∀ x, deriv (psi j t) x ≤ upper) :
    ∃ (sigma : ℕ → ℕ)
      (Dn : ℕ → C(Icc (0 : ℝ) S, C(AddCircle L, ℝ)))
      (d : C(Icc (0 : ℝ) S, C(AddCircle L, ℝ))),
      StrictMono sigma ∧
      Tendsto (fun j => Vn (sigma j)) atTop (𝓝 V) ∧
      Tendsto Dn atTop (𝓝 d) ∧
      (∀ j (t : Icc (0 : ℝ) S) (x : ℝ),
        Dn j t (x : AddCircle L) = psi (sigma j) t x - x) ∧
      d ⟨0, le_rfl, hS.le⟩ = 0 := by
  classical
  obtain ⟨B, hB, w, hw, hwrep, hwbound⟩ :=
    exists_uniform_spectral_labelVelocity_L2_bound F hU hρ hS hSb hK hKU
      Vn V hV qn hq hqzero hphase hjets
  have hwopen (j : ℕ) : ContinuousOn (w j) (Ioo 0 S) :=
    (hw j).mono Ioo_subset_Icc_self
  have hode (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 S) (x : ℝ) :
      HasDerivAt (fun r => psi j r x) (w j t (psi j t x : AddCircle L)) t := by
    rw [hwrep j t (Ioo_subset_Icc_self ht) (psi j t x)]
    exact htime j t ht x
  have hnorm (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 S) :
      ‖ContinuousMap.toLp 2 haarAddCircle ℝ (w j t)‖ ≤ B :=
    hwbound j t (Ioo_subset_Icc_self ht)
  obtain ⟨D, _velocity, hDc, hDrep, _hVc, _hVrep, _hDder, _hVbound, _hL2⟩ :=
    exists_periodicLabel_displacement_L2_control (P := L) (a := 0) (b := S)
      hS psi w hpsi hshift hwopen hode hell hB hlower hnorm
  obtain ⟨sigma, d0, hsigma, hdc, hdzero, _hphic, _hperiod, _hinc, huniform⟩ :=
    exists_uniform_periodicLabel_subsequence (P := L) (a := 0) (b := S)
      hS psi w hpsi hshift hwopen hode hell hB hlower hnorm hupper hinitial
  let Dn : ℕ → C(Icc (0 : ℝ) S, C(AddCircle L, ℝ)) := fun j =>
    ⟨fun t => D (sigma j) t, (hDc (sigma j)).domRestrict⟩
  let d : C(Icc (0 : ℝ) S, C(AddCircle L, ℝ)) :=
    ⟨fun t => d0 t, hdc.domRestrict⟩
  have hconv : Tendsto Dn atTop (𝓝 d) := by
    apply Metric.tendsto_atTop.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := huniform (eps / 2) (half_pos heps)
    refine ⟨N, ?_⟩
    intro j hj
    have hdist : dist (Dn j) d ≤ eps / 2 := by
      apply (ContinuousMap.dist_le (half_pos heps).le).mpr
      intro t
      apply (ContinuousMap.dist_le (half_pos heps).le).mpr
      intro z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      have hx : |psi (sigma j) t x - (x + d0 t (x : AddCircle L))| < eps / 2 :=
        hN j hj t t.property x
      change dist (D (sigma j) t (x : AddCircle L)) (d0 t (x : AddCircle L)) ≤ eps / 2
      rw [Real.dist_eq, hDrep (sigma j) t t.property x]
      simpa only [sub_sub] using hx.le
    exact hdist.trans_lt (half_lt_self heps)
  refine ⟨sigma, Dn, d, hsigma, hV.comp hsigma.tendsto_atTop, hconv, ?_, ?_⟩
  · intro j t x
    exact hDrep (sigma j) t t.property x
  · change d0 0 = 0
    exact hdzero

end PoincareConjecture.M63
