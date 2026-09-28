import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.Riemannian.PathELength











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem edist_add_escape_le_add_shortcut_of_path_crossing
    (g : RiemannianMetric n M)
    {b p x : M} {S : Set M} {c e : ℝ≥0∞}
    (hcross : ∀ gamma : ℝ → M, gamma 0 = b → gamma 1 = p →
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Icc (0 : ℝ) 1) →
        ∃ t ∈ Icc (0 : ℝ) 1, gamma t ∈ S)
    (hescape : ∀ y ∈ S, e ≤ g.edist y p)
    (hshort : ∀ y ∈ S, g.edist y x ≤ c) :
    g.edist b x + e ≤ g.edist b p + c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ENNReal.le_of_forall_pos_le_add
  intro eta heta _
  by_cases hp : g.edist b p = ⊤
  · simp only [hp, top_add, le_top]
  obtain ⟨gamma, h0, h1, hgamma, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt
      (ENNReal.lt_add_right hp (ENNReal.coe_ne_zero.mpr heta.ne'))
  obtain ⟨t, ht, htS⟩ := hcross gamma h0 h1 hgamma
  have hprefix : g.edist b (gamma t) ≤ g.pathELength gamma 0 t :=
    Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Icc_subset_Icc le_rfl ht.2)) h0 rfl ht.1
  have hsuffix : g.edist (gamma t) p ≤ g.pathELength gamma t 1 :=
    Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Icc_subset_Icc ht.1 le_rfl)) rfl h1 ht.2
  calc
    g.edist b x + e ≤
        (g.pathELength gamma 0 t + c) + g.pathELength gamma t 1 :=
      add_le_add
        (Manifold.riemannianEDist_triangle.trans (add_le_add hprefix (hshort _ htS)))
        ((hescape _ htS).trans hsuffix)
    _ = (g.pathELength gamma 0 t + g.pathELength gamma t 1) + c := by ac_rfl
    _ = g.pathELength gamma 0 1 + c := by
      rw [show g.pathELength gamma 0 t + g.pathELength gamma t 1 =
        g.pathELength gamma 0 1 from Manifold.pathELength_add ht.1 ht.2]
    _ ≤ (g.edist b p + eta) + c := add_le_add hlength.le le_rfl
    _ = (g.edist b p + c) + eta := by ac_rfl





theorem edist_add_le_of_path_crossing (g : RiemannianMetric n M)
    {b p x : M} {S : Set M} {c e delta : ℝ≥0∞} (hc : c ≠ ⊤)
    (hgap : c + delta ≤ e)
    (hcross : ∀ gamma : ℝ → M, gamma 0 = b → gamma 1 = p →
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma (Icc (0 : ℝ) 1) →
        ∃ t ∈ Icc (0 : ℝ) 1, gamma t ∈ S)
    (hescape : ∀ y ∈ S, e ≤ g.edist y p)
    (hshort : ∀ y ∈ S, g.edist y x ≤ c) :
    g.edist b x + delta ≤ g.edist b p := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro R hR
  obtain ⟨gamma, h0, h1, hgamma, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hR
  obtain ⟨t, ht, htS⟩ := hcross gamma h0 h1 hgamma
  have hprefix : g.edist b (gamma t) ≤ g.pathELength gamma 0 t :=
    Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Icc_subset_Icc le_rfl ht.2)) h0 rfl ht.1
  have hsuffix : g.edist (gamma t) p ≤ g.pathELength gamma t 1 :=
    Manifold.riemannianEDist_le_pathELength
      (hgamma.mono (Icc_subset_Icc ht.1 le_rfl)) rfl h1 ht.2
  have hshortcut : g.edist b x ≤ g.pathELength gamma 0 t + c :=
    Manifold.riemannianEDist_triangle.trans (add_le_add hprefix (hshort _ htS))
  have hsum : g.edist b x + (c + delta) ≤ g.pathELength gamma 0 1 + c := by
    calc
      _ ≤ g.edist b x + e := add_le_add le_rfl hgap
      _ ≤ (g.pathELength gamma 0 t + c) + g.pathELength gamma t 1 :=
        add_le_add hshortcut ((hescape _ htS).trans hsuffix)
      _ = (g.pathELength gamma 0 t + g.pathELength gamma t 1) + c := by ac_rfl
      _ = _ := by rw [show g.pathELength gamma 0 t + g.pathELength gamma t 1 =
        g.pathELength gamma 0 1 from Manifold.pathELength_add ht.1 ht.2]
  apply ENNReal.le_of_add_le_add_right hc
  calc
    (g.edist b x + delta) + c = g.edist b x + (c + delta) := by ac_rfl
    _ ≤ g.pathELength gamma 0 1 + c := hsum
    _ ≤ R + c := add_le_add hlength.le le_rfl

end PoincareConjecture.RiemannianMetric
