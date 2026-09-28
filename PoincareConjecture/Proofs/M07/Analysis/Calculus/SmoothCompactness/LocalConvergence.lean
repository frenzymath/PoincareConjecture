import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Uniqueness

set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem eqOn_iteratedFDeriv_of_isOpen
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : Set E} (hV : IsOpen V) {f g : E → F} (heq : EqOn f g V) (m : ℕ) :
    EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) V := by
  intro x hx
  have hnear : f =ᶠ[𝓝 x] g := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact heq hy
  exact (hnear.iteratedFDeriv ℝ m).self_of_nhds

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → F}
    {F₀ : EuclideanSpace ℝ (Fin d) → F}

theorem tendstoUniformlyOn_iteratedFDeriv_of_local_convergence
    (hU : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ m K, IsCompact K → K ⊆ V →
        TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
          (iteratedFDeriv ℝ m F₀) atTop K)
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m F₀) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp ?_ K hKU hK
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨V, hV, hxV, _, hjet⟩ := hlocal x hx
  obtain ⟨C, ⟨hCn, hC⟩, hCV⟩ :=
    (compact_basis_nhds x).mem_iff.mp (hV.mem_nhds hxV)
  exact ⟨C, nhdsWithin_le_nhds hCn, hjet m C hC hCV⟩

theorem tendstoUniformlyOn_iteratedFDeriv_of_local_models
    (hU : IsOpen U)
    (hlocal : ∀ x ∈ U, ∃ V : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ g : ℕ → EuclideanSpace ℝ (Fin d) → F,
        ∃ G : EuclideanSpace ℝ (Fin d) → F,
          (∀ᶠ k in atTop, EqOn (f k) (g k) V) ∧ EqOn F₀ G V ∧
          ∀ m K, IsCompact K → K ⊆ V →
            TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (g k))
              (iteratedFDeriv ℝ m G) atTop K)
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m F₀) atTop K := by
  apply tendstoUniformlyOn_iteratedFDeriv_of_local_convergence hU ?_ m hK hKU
  intro x hx
  obtain ⟨V, hV, hxV, hVU, g, G, heq, hlimit, hjet⟩ := hlocal x hx
  refine ⟨V, hV, hxV, hVU, ?_⟩
  intro l C hC hCV
  apply ((hjet l C hC hCV).congr ?_).congr_right
    ((eqOn_iteratedFDeriv_of_isOpen hV hlimit.symm l).mono hCV)
  exact heq.mono fun _ hk => (eqOn_iteratedFDeriv_of_isOpen hV hk.symm l).mono hCV

end Poincare.Analysis.Calculus
