import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.ConstraintsCompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology
namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_contMDiff_directional_approx_on_compact_subset_of_local
    (D : LeviCivitaData g) {T S : Set M} (hT : IsCompact T) (hST : S ⊆ T)
    {d : M → ℝ} (hd : ContinuousOn d T)
    {L H V : ℝ} (hL : 0 ≤ L) (hV : 0 ≤ V)
    {ι : Type*} (v : ι → (x : M) → TangentSpace (𝓡 n) x)
    (lo hi : ι → M → ℝ)
    (hv : ∀ i x, x ∈ S → g.tangentNorm x (v i x) ≤ V)
    (hlocal : ∀ x ∈ T, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ e : ℝ, 0 < e → ∃ f : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U ∧
        (∀ y ∈ U, |f y - d y| ≤ e) ∧
        (∀ y ∈ U, g.tangentNorm y (D.gradient f y) ≤ L) ∧
        (∀ y ∈ U, ∀ w : TangentSpace (𝓡 n) y,
          D.hessian f y w w ≤ H * g.inner y w w) ∧
        ∀ i y, y ∈ U → y ∈ S →
          lo i y ≤ mvfderiv (𝓡 n) f y (v i y) ∧
            mvfderiv (𝓡 n) f y (v i y) ≤ hi i y)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      (∀ x ∈ T, |rho x - d x| ≤ ε) ∧
      (∀ x ∈ T, g.tangentNorm x (D.gradient rho x) ≤ L + η) ∧
      (∀ x ∈ T, ∀ w : TangentSpace (𝓡 n) x,
        D.hessian rho x w w ≤ (H + η) * g.inner x w w) ∧
      ∀ i x, x ∈ S →
        lo i x - η ≤ mvfderiv (𝓡 n) rho x (v i x) ∧
          mvfderiv (𝓡 n) rho x (v i x) ≤ hi i x + η := by
  classical
  let v' := fun i x => if x ∈ S then v i x else 0
  let lo' := fun i x => if x ∈ S then lo i x else 0
  let hi' := fun i x => if x ∈ S then hi i x else 0
  have hv' (i : ι) (x : M) (_hx : x ∈ T) : g.tangentNorm x (v' i x) ≤ V := by
    by_cases hx : x ∈ S
    · simpa only [v', if_pos hx] using hv i x hx
    · simpa [v', hx, RiemannianMetric.tangentNorm] using hV
  obtain ⟨rho, hrho, herr, hgrad, hess, hdir⟩ :=
    D.exists_contMDiff_directional_approx_on_compact_of_local hT hd hL hV v' lo' hi'
      hv' (by
        intro x hx
        obtain ⟨U, hU, hxU, ha⟩ := hlocal x hx
        refine ⟨U, hU, hxU, ?_⟩
        intro e he
        obtain ⟨f, hf, herr, hgrad, hess, hdir⟩ := ha e he
        refine ⟨f, hf, herr, hgrad, hess, ?_⟩
        intro i y hy _
        by_cases hyS : y ∈ S
        · simpa only [v', lo', hi', if_pos hyS] using hdir i y hy hyS
        · simp [v', lo', hi', hyS]) hε hη
  refine ⟨rho, hrho, herr, hgrad, hess, ?_⟩
  intro i x hx
  simpa only [v', lo', hi', if_pos hx] using hdir i x (hST hx)

end PoincareConjecture.LeviCivitaData
