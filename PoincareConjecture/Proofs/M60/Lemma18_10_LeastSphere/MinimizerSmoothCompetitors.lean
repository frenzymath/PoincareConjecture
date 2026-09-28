import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSmoothingChart
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaToEnergy
import PoincareConjecture.Proofs.M40.Mathlib.SmoothingCharts
import Mathlib.Geometry.Manifold.Metrizable

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem suC1_exists_smooth_density_approximation
    (g : RiemannianMetric n M) (f₀ : C(UnitTwoSphere, M))
    (hf₀ : ContMDiff (𝓡 2) (𝓡 n) 1 f₀) {eta : ℝ} (heta : 0 < eta) :
    ∃ h : C(UnitTwoSphere, M), ContMDiff (𝓡 2) (𝓡 n) ∞ h ∧ h.Homotopic f₀ ∧
      ∀ x, |m60SphereIntrinsicEnergy g h x - m60SphereIntrinsicEnergy g f₀ x| < eta := by
  classical
  obtain ⟨N, c, rho, margin, hmargin, hsupp, hrho, hcover, hvalid⟩ :=
    M40.exists_finite_smoothing_charts (E := LoopPlane)
      (F := EuclideanSpace ℝ (Fin n)) f₀
  let W : Fin N → Set UnitTwoSphere := fun i => {x | (rho i : UnitTwoSphere → ℝ) =ᶠ[𝓝 x] 1}
  have hstep (i : Fin N) (f : C(UnitTwoSphere, M))
      (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
      (hclose : ∀ x, dist (f x) (f₀ x) < margin)
      (epsilon theta : ℝ) (hepsilon : 0 < epsilon) (htheta : 0 < theta) :
      ∃ h : C(UnitTwoSphere, M), ContMDiff (𝓡 2) (𝓡 n) 1 h ∧
        (∀ x ∈ W i, ContMDiffAt (𝓡 2) (𝓡 n) ∞ h x) ∧
        (∀ x, ContMDiffAt (𝓡 2) (𝓡 n) ∞ f x → ContMDiffAt (𝓡 2) (𝓡 n) ∞ h x) ∧
        h.Homotopic f ∧ (∀ x, dist (h x) (f x) < epsilon) ∧
        ∀ x, |m60SphereIntrinsicEnergy g h x - m60SphereIntrinsicEnergy g f x| < theta := by
    apply suC1_exists_chart_smoothing g (c i) (f₀ (c i))
      (rho i) (hrho i) (fun _ => (rho i).mem_Icc) (hsupp i) f hf ?_ hepsilon htheta
    exact hvalid f (fun x => by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hmargin).mpr (hclose x)) i
  have hfinite : ∀ A : Finset (Fin N), ∀ epsilon theta : ℝ,
      0 < epsilon → epsilon ≤ margin → 0 < theta →
      ∃ h : C(UnitTwoSphere, M), ContMDiff (𝓡 2) (𝓡 n) 1 h ∧
        (∀ i ∈ A, ∀ x ∈ W i, ContMDiffAt (𝓡 2) (𝓡 n) ∞ h x) ∧
        h.Homotopic f₀ ∧ (∀ x, dist (h x) (f₀ x) < epsilon) ∧
        ∀ x, |m60SphereIntrinsicEnergy g h x - m60SphereIntrinsicEnergy g f₀ x| < theta := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro epsilon theta hepsilon _ htheta
      exact ⟨f₀, hf₀, by simp, .refl f₀, fun _ => by simpa using hepsilon,
        fun _ => by simpa using htheta⟩
    | @insert i A _ ih =>
      intro epsilon theta hepsilon hemargin htheta
      obtain ⟨f, hf, hfsmooth, hfhom, hfclose, hfenergy⟩ :=
        ih (epsilon / 2) (theta / 2) (half_pos hepsilon) (by linarith) (half_pos htheta)
      obtain ⟨h, hh, hhsmooth, hhpreserve, hhhom, hhclose, hhenergy⟩ := hstep i f hf
        (fun x => (hfclose x).trans_le (by linarith))
        (epsilon / 2) (theta / 2) (half_pos hepsilon) (half_pos htheta)
      refine ⟨h, hh, ?_, hhhom.trans hfhom, ?_, ?_⟩
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hhsmooth x hx
        · exact hhpreserve x (hfsmooth j hj x hx)
      · intro x
        exact (dist_triangle (h x) (f x) (f₀ x)).trans_lt
          ((add_lt_add (hhclose x) (hfclose x)).trans_eq (add_halves epsilon))
      · intro x
        exact (abs_sub_le (m60SphereIntrinsicEnergy g h x)
          (m60SphereIntrinsicEnergy g f x) (m60SphereIntrinsicEnergy g f₀ x)).trans_lt
          ((add_lt_add (hhenergy x) (hfenergy x)).trans_eq (add_halves theta))
  obtain ⟨h, -, hh, hhom, -, henergy⟩ := hfinite Finset.univ margin eta hmargin le_rfl heta
  refine ⟨h, ?_, hhom, henergy⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact hh i (Finset.mem_univ i) x hi

theorem suC1_exists_smooth_energy_approximation
    (g : RiemannianMetric n M) (f : C(UnitTwoSphere, M))
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) {eta : ℝ} (heta : 0 < eta) :
    ∃ h : C(UnitTwoSphere, M), ContMDiff (𝓡 2) (𝓡 n) ∞ h ∧ h.Homotopic f ∧
      m60SphereEnergy g h < m60SphereEnergy g f + eta := by
  obtain ⟨h, hh, hhom, he⟩ := suC1_exists_smooth_density_approximation g f hf
    (div_pos heta (show 0 < 8 * Real.pi by positivity))
  refine ⟨h, hh, hhom, ?_⟩
  have hi := suC1_energy_le_of_density_le g hf (hh.of_le (by simp))
    (eta / (8 * Real.pi)) (fun x => by have := (abs_lt.mp (he x)).2; linarith)
  have heq : eta / (8 * Real.pi) * (4 * Real.pi) = eta / 2 := by
    field_simp
    ring
  rw [heq] at hi
  linarith

end PoincareConjecture.M60

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M]

theorem m60SphereEnergy_smooth_infimum (g : RiemannianMetric n M) :
    sInf (m60SphereEnergy g '' {f | ContMDiff (𝓡 2) (𝓡 n) ∞ f ∧
      ¬ IsNullHomotopicSphere f}) =
    sInf (m60SphereEnergy g '' {f | ContMDiff (𝓡 2) (𝓡 n) 1 f ∧
      ¬ IsNullHomotopicSphere f}) := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 n) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  let S : Set (UnitTwoSphere → M) :=
    {f | ContMDiff (𝓡 2) (𝓡 n) ∞ f ∧ ¬ IsNullHomotopicSphere f}
  let T : Set (UnitTwoSphere → M) :=
    {f | ContMDiff (𝓡 2) (𝓡 n) 1 f ∧ ¬ IsNullHomotopicSphere f}
  change sInf (m60SphereEnergy g '' S) = sInf (m60SphereEnergy g '' T)
  have hST : S ⊆ T := fun _ h => ⟨h.1.of_le (by simp), h.2⟩
  have hS : BddBelow (m60SphereEnergy g '' S) := ⟨0, by
    rintro _ ⟨f, -, rfl⟩; exact m60SphereEnergy_nonneg g f⟩
  have hT : BddBelow (m60SphereEnergy g '' T) := ⟨0, by
    rintro _ ⟨f, -, rfl⟩; exact m60SphereEnergy_nonneg g f⟩
  have hsmooth (f : UnitTwoSphere → M) (hf : f ∈ T) {eta : ℝ} (heta : 0 < eta) :
      ∃ h ∈ S, m60SphereEnergy g h < m60SphereEnergy g f + eta := by
    let f' : C(UnitTwoSphere, M) := ⟨f, hf.1.continuous⟩
    obtain ⟨h, hh, hhom, he⟩ := M60.suC1_exists_smooth_energy_approximation g f' hf.1 heta
    refine ⟨h, ⟨hh, ?_⟩, he⟩
    rintro ⟨_, y, hnull⟩
    exact hf.2 ⟨hf.1.continuous, y, hhom.symm.trans hnull⟩
  by_cases hne : T.Nonempty
  · obtain ⟨f, hf⟩ := hne
    obtain ⟨h, hh, -⟩ := hsmooth f hf (show (0 : ℝ) < 1 by norm_num)
    have hSne : S.Nonempty := ⟨h, hh⟩
    apply le_antisymm
    · refine le_csInf (show (m60SphereEnergy g '' T).Nonempty from
        ⟨m60SphereEnergy g f, f, hf, rfl⟩) ?_
      rintro _ ⟨f, hf, rfl⟩
      by_contra hn
      obtain ⟨h, hh, he⟩ := hsmooth f hf
        (sub_pos.mpr (lt_of_not_ge hn))
      have hi := csInf_le hS ⟨h, hh, rfl⟩
      linarith
    · refine le_csInf (hSne.image _) ?_
      rintro _ ⟨h, hh, rfl⟩
      exact csInf_le hT ⟨h, hST hh, rfl⟩
  · have hTempty := Set.not_nonempty_iff_eq_empty.mp hne
    have hSempty : S = ∅ := subset_eq_empty (hTempty ▸ hST) rfl
    rw [hSempty, hTempty]

theorem m60SphereArea_smooth_energy_infimum (g : RiemannianMetric n M) :
    sInf (m60SphereArea g '' {f | ContMDiff (𝓡 2) (𝓡 n) 1 f ∧
      ¬ IsNullHomotopicSphere f}) =
    sInf (m60SphereEnergy g '' {f | ContMDiff (𝓡 2) (𝓡 n) ∞ f ∧
      ¬ IsNullHomotopicSphere f}) := by
  rw [m60SphereEnergy_smooth_infimum g]
  exact m60SphereArea_energy_infimum g

end PoincareConjecture

end
