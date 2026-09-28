import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLocalAreaStep
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFiniteChartCover














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
local notation "E" => EuclideanSpace ℝ (Fin n)





theorem scalar_exists_relative_area_approximation
    (g : RiemannianMetric n M) (f : Plane → M) {O W K S : Set Plane}
    (hO : IsOpen O) (hW : IsOpen W) (hWO : W ⊆ O) (hWS : W ⊆ S)
    (hK : IsCompact K) (hKW : K ⊆ W) (hS : MeasurableSet S)
    (hf : ContinuousOn f O) (hlocal : ScalarLocallyChartLipschitz (n := n) f O)
    (harea : IntegrableOn (m60AreaDensity g f) S) {eps : ℝ} (heps : 0 < eps) :
    ∃ F : Plane → M,
      ContinuousOn F O ∧ ScalarLocallyChartLipschitz (n := n) F O ∧
      (∀ x, x ∉ W → F =ᶠ[𝓝 x] f) ∧
      (∀ x, ContMDiffAt (𝓡 2) (𝓡 n) 1 f x → ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
      (∀ x ∈ K, ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
      (∀ x, dist (F x) (f x) < eps) ∧
      IntegrableOn (m60AreaDensity g F) S ∧
      (∫ x in S, m60AreaDensity g F x) < (∫ x in S, m60AreaDensity g f x) + eps := by
  classical
  obtain ⟨d, c, rho, margin, hmargin, hrho, hrange, hcompact, hsupp, hcover, hvalid⟩ :=
    scalar_exists_finite_relative_charts (F := E) f hK hW hKW (hf.mono hWO)
  have hfinite : ∀ A : Finset (Fin d), ∀ delta : ℝ, 0 < delta → delta ≤ margin →
      ∃ F : Plane → M,
        ContinuousOn F O ∧ ScalarLocallyChartLipschitz (n := n) F O ∧
        (∀ i ∈ A, ∀ x, rho i =ᶠ[𝓝 x] 1 → ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
        (∀ x, ContMDiffAt (𝓡 2) (𝓡 n) 1 f x → ContMDiffAt (𝓡 2) (𝓡 n) 1 F x) ∧
        (∀ x, x ∉ W → F =ᶠ[𝓝 x] f) ∧
        (∀ x, dist (F x) (f x) < delta) ∧
        IntegrableOn (m60AreaDensity g F) S ∧
        (∫ x in S, m60AreaDensity g F x) <
          (∫ x in S, m60AreaDensity g f x) + delta := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro delta hdelta _
      exact ⟨f, hf, hlocal, by simp, fun _ hx => hx, fun _ _ => EventuallyEq.rfl,
        fun _ => by simpa using hdelta, harea, by linarith⟩
    | @insert i A _ ih =>
      intro delta hdelta hdmargin
      obtain ⟨F, hFc, hFlocal, hFs, hFp, hFa, hFclose, hFI, hFA⟩ :=
        ih (delta / 2) (half_pos hdelta) (by linarith)
      obtain ⟨G, hGc, hGlocal, hGa, hGp, hGs, hGclose, hGI, hGA⟩ :=
        scalar_exists_local_area_step g (chartAt E (c i))
          contMDiffOn_chart contMDiffOn_chart_symm F hO hFc hFlocal
          (hrho i) (hcompact i) (hrange i) ((hsupp i).trans hWO)
          (hvalid F (fun x => (hFclose x).trans_le (by linarith)) i)
          hS ((hsupp i).trans hWS) hFI (half_pos hdelta)
      refine ⟨G, hGc, hGlocal, ?_, (fun x hx => hGp x (hFp x hx)), ?_, ?_, hGI, ?_⟩
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hGs x hx
        · exact hGp x (hFs j hj x hx)
      · intro x hx
        exact (hGa x (fun hxs => hx (hsupp i hxs))).trans (hFa x hx)
      · intro x
        exact (dist_triangle (G x) (F x) (f x)).trans_lt
          ((add_lt_add (hGclose x) (hFclose x)).trans_eq (add_halves delta))
      · linarith
  obtain ⟨F, hFc, hFlocal, hFs, hFp, hFa, hFclose, hFI, hFA⟩ :=
    hfinite Finset.univ (min margin eps) (lt_min hmargin heps) (min_le_left _ _)
  refine ⟨F, hFc, hFlocal, hFa, hFp, ?_,
    (fun x => (hFclose x).trans_le (min_le_right _ _)), hFI,
    hFA.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact hFs i (Finset.mem_univ i) x hi

end PoincareConjecture.M64Uniformization
