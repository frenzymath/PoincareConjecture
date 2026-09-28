import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.PartialTraceEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.TimeTransport.Smooth








noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace Poincare.RicciFlow.Splitting

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]


theorem partialTrace_eq_of_isometry (k : ℕ) (A : E →L[ℝ] E) (B : H →L[ℝ] H)
    (P : E ≃ₗᵢ[ℝ] H)
    (h : ∀ v, inner ℝ (A v) v = inner ℝ (B (P v)) (P v)) :
    partialTrace k A = partialTrace k B := by
  unfold partialTrace
  congr 1
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨P ∘ v, P.toLinearIsometry.orthonormal_comp_iff.mpr hv, ?_⟩
    simp only [frameTrace, Function.comp_apply, h]
  · rintro ⟨v, hv, rfl⟩
    refine ⟨P.symm ∘ v, P.symm.toLinearIsometry.orthonormal_comp_iff.mpr hv, ?_⟩
    simp only [frameTrace, Function.comp_apply, h, P.apply_symm_apply]

private def matrixOperator {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (c : ι → ι → ℝ) : E →L[ℝ] E :=
  ∑ i, ∑ j, c i j • (innerSL ℝ (e i)).smulRight (e j)

private theorem matrixOperator_basis {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (c : ι → ι → ℝ) (i : ι) :
    matrixOperator e c (e i) = ∑ j, c i j • e j := by
  classical
  simp [matrixOperator, OrthonormalBasis.inner_eq_ite]

private theorem matrixOperator_inner_basis {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (c : ι → ι → ℝ) (i j : ι) :
    inner ℝ (matrixOperator e c (e i)) (e j) = c i j := by
  classical
  rw [matrixOperator_basis]
  simp [sum_inner, real_inner_smul_left, e.inner_eq_ite]

private theorem matrixOperator_pairing {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (c : ι → ι → ℝ)
    (B : H →L[ℝ] H) (P : E ≃ₗᵢ[ℝ] H)
    (hc : ∀ i j, c i j = inner ℝ (B (P (e i))) (P (e j))) (v : E) :
    inner ℝ (matrixOperator e c v) v = inner ℝ (B (P v)) (P v) := by
  have hbas (i : ι) : matrixOperator e c (e i) = P.symm (B (P (e i))) := by
    apply e.repr.injective
    ext j
    simp only [OrthonormalBasis.repr_apply_apply]
    rw [real_inner_comm, matrixOperator_inner_basis, hc]
    rw [← P.inner_map_map, P.apply_symm_apply]
    exact real_inner_comm _ _
  have heq (x : E) : matrixOperator e c x = P.symm (B (P x)) := by
    rw [← e.sum_repr x]
    simp only [map_sum, map_smul, hbas]
  rw [heq]
  rw [← P.inner_map_map, P.apply_symm_apply]

private theorem continuousOn_matrixOperator {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] (e : OrthonormalBasis ι ℝ E) (c : X → ι → ι → ℝ)
    {S : Set X} (hc : ∀ i j, ContinuousOn (fun q => c q i j) S) :
    ContinuousOn (fun q => matrixOperator e (c q)) S := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (hc i j).smul continuousOn_const

end Poincare.RicciFlow.Splitting

universe u

namespace PoincareConjecture.RicciFlow.Splitting

private theorem exists_linearIsometryEquiv_of_basis_pairings
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (w : ι → H)
    (hw : ∀ i j, inner ℝ (w i) (w j) = inner ℝ (b i) (b j))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ H) :
    ∃ P : E ≃ₗᵢ[ℝ] H, ∀ i, P (b i) = w i := by
  classical
  let L : E →ₗ[ℝ] H := b.toBasis.constr ℝ w
  have hL : Orthonormal ℝ (L ∘ b.toBasis) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [Function.comp_apply, L, Module.Basis.constr_basis]
    exact (hw i j).trans ((orthonormal_iff_ite.mp b.orthonormal) i j)
  let f := L.isometryOfOrthonormal b.orthonormal hL
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp f.injective
  refine ⟨LinearIsometryEquiv.ofSurjective f hsurj, ?_⟩
  intro i
  exact b.toBasis.constr_basis ℝ w i

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem exists_smooth_local_ricci_transport_frame [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b)) (p : M) :
    ∃ (U : Set M) (Y : Fin n → ℝ → (x : M) → TangentSpace (𝓡 n) x),
      IsOpen U ∧ p ∈ U ∧
      (∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun q : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2
          (Y i q.1 q.2)) (Icc a b ×ˢ univ)) ∧
      (∀ t ∈ Icc a b, ∀ x ∈ U, ∀ i j,
        (F.metric t).inner x (Y i t x) (Y j t x) = if i = j then 1 else 0) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  obtain ⟨r, W, hr, _, hW, hinit, _, P, hP⟩ :=
    (F.connection b).exists_radialParallelIsometries p
  let V := LeviCivitaData.radialNeighborhood (n := n) p r
  have hV : IsOpen V := LeviCivitaData.isOpen_radialNeighborhood p r
  have hpV : p ∈ V := LeviCivitaData.mem_radialNeighborhood p hr
  obtain ⟨χ, -, hχV⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) p).mem_iff.mp (hV.mem_nhds hpV)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp
    (Filter.Eventually.and (hV.mem_nhds hpV) χ.eventuallyEq_one)
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) p) = n :=
    finrank_euclideanSpace_fin
  let ι : Fin n → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) p)) :=
    Fin.cast hdim.symm
  let Z : Fin n → (x : M) → TangentSpace (𝓡 n) x := fun i =>
    χ.toFun • LeviCivitaData.fieldFromCenteredCoordinates p (W (ι i))
  have hZ (i : Fin n) : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Z i)) := by
    apply ContMDiffOn.smul_section_of_tsupport χ.contMDiff.contMDiffOn hV hχV
    intro x hx
    exact (LeviCivitaData.contMDiffAt_fieldFromCenteredCoordinates p
      (hW (ι i)).contDiffAt hx.1).contMDiffWithinAt
  choose T hTb hTode hTpair hTinv using exists_terminal_ricci_transport hC hab F
  let Y : Fin n → ℝ → (x : M) → TangentSpace (𝓡 n) x :=
    fun i t x => T x t (Z i x)
  have hYb (i : Fin n) : Y i b = Z i := by
    funext x
    simp only [Y, hTb, ContinuousLinearMap.id_apply]
  refine ⟨U, Y, hU, hpU, ?_, ?_⟩
  · intro i
    apply ricci_transport_contMDiffOn hab F (Y i)
    · simpa only [hYb] using hZ i
    · intro x t ht
      exact hTode x t ht (Z i x)
  · intro t ht x hx i j
    rw [hTpair x t ht]
    have hxV : x ∈ V := (hUsub hx).1
    have hχx : χ x = 1 := (hUsub hx).2
    have hPi (l : Fin n) :
        P ⟨x, hxV⟩ ((F.metric b).orthonormalBasis p (ι l)) = Z l x := by
      rw [hP]
      simp [Z, hχx]
    rw [← hPi i, ← hPi j]
    change inner ℝ (P ⟨x, hxV⟩ _) (P ⟨x, hxV⟩ _) = _
    rw [(P ⟨x, hxV⟩).inner_map_map]
    simp only [OrthonormalBasis.inner_eq_ite, ι, Fin.cast_inj]


theorem continuousOn_ricci_pairing (hab : a < b) (F : RicciFlow n M (Icc a b))
    (X Y : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2 (X q.1 q.2))
      (Icc a b ×ˢ univ))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2 (Y q.1 q.2))
      (Icc a b ×ˢ univ)) :
    ContinuousOn (fun q : ℝ × M =>
      (F.connection q.1).ricci q.2 (X q.1 q.2) (Y q.1 q.2)) (Icc a b ×ˢ univ) := by
  have h : ContinuousOn (fun q : ℝ × M => (F.metric q.1).inner q.2
      (ricciEndomorphism F q.2 q.1 (X q.1 q.2)) (Y q.1 q.2)) (Icc a b ×ˢ univ) := by
    intro q hq
    have hRX := (contMDiffOn_ricciEndomorphism hab F q hq).clm_bundle_apply (hX q hq)
    have hpair := (F.smooth q hq).clm_bundle_apply₂
      (F₃ := ℝ) (E₃ := fun _ : M => ℝ) hRX (hY q hq)
    exact (contMDiffWithinAt_totalSpace.mp hpair).2.continuousWithinAt
  apply h.congr
  intro q hq
  exact (inner_ricciEndomorphism hab F q.2 hq.1 _ _).symm



theorem ricciPartialTrace_continuousOn [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b)) {k : ℕ} (hk : k ≤ n) :
    ContinuousOn (fun q : ℝ × M => ricciPartialTrace (F.connection q.1) k q.2)
      (Icc a b ×ˢ univ) := by
  classical
  rintro ⟨t, p⟩ ⟨ht, _⟩
  obtain ⟨U, Y, hU, hpU, hY, hpair⟩ :=
    exists_smooth_local_ricci_transport_frame hC hab F p
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let c : (ℝ × M) → Fin n → Fin n → ℝ := fun q i j =>
    (F.connection q.1).ricci q.2 (Y i q.1 q.2) (Y j q.1 q.2)
  have hc (i j : Fin n) : ContinuousOn (fun q => c q i j) (Icc a b ×ˢ univ) :=
    continuousOn_ricci_pairing hab F (Y i) (Y j) (hY i) (hY j)
  let A := fun q => Poincare.RicciFlow.Splitting.matrixOperator e (c q)
  have hA : ContinuousOn A (Icc a b ×ˢ univ) :=
    Poincare.RicciFlow.Splitting.continuousOn_matrixOperator e c hc
  have hkE : k ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace_fin] using hk
  have hcont := (Poincare.RicciFlow.Splitting.continuous_partialTrace hkE).comp_continuousOn hA
  have heq (q : ℝ × M) (htq : q.1 ∈ Icc a b) (hxq : q.2 ∈ U) :
      ricciPartialTrace (F.connection q.1) k q.2 =
        Poincare.RicciFlow.Splitting.partialTrace k (A q) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric q.1).toRiemannianMetric⟩
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) q.2) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) q.2
    obtain ⟨P, hP⟩ := exists_linearIsometryEquiv_of_basis_pairings e
      (fun i => Y i q.1 q.2)
      (by intro i j; exact (hpair q.1 htq q.2 hxq i j).trans (e.inner_eq_ite i j).symm)
      (by rfl)
    symm
    apply Poincare.RicciFlow.Splitting.partialTrace_eq_of_isometry k (A q)
      (metricRicciOperator (F.connection q.1) q.2) P
    apply Poincare.RicciFlow.Splitting.matrixOperator_pairing
    intro i j
    rw [hP, hP]
    exact (metricRicciOperator_inner (F.connection q.1) q.2 _ _).symm
  apply (hcont (t, p) ⟨ht, mem_univ p⟩).congr_of_eventuallyEq_of_mem _ ⟨ht, mem_univ p⟩
  have hUnhds : ∀ᶠ q : ℝ × M in 𝓝 (t, p), q.2 ∈ U :=
    continuousAt_snd.preimage_mem_nhds (hU.mem_nhds hpU)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hUnhds] with q hq hqU
  exact heq q hq.1 hqU


theorem ricciPartialTrace_continuousOn_prod [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b)) {k : ℕ} (hk : k ≤ n) :
    ContinuousOn (fun q : M × ℝ => ricciPartialTrace (F.connection q.2) k q.1)
      (univ ×ˢ Icc a b) := by
  have hs : ContinuousOn (Prod.swap : M × ℝ → ℝ × M) (univ ×ˢ Icc a b) :=
    continuous_swap.continuousOn
  have hm : MapsTo (Prod.swap : M × ℝ → ℝ × M)
      (univ ×ˢ Icc a b) (Icc a b ×ˢ univ) := fun q hq => ⟨hq.2, hq.1⟩
  have h := (ricciPartialTrace_continuousOn hC hab F hk).comp hs hm
  simpa only [Function.comp_def, Prod.swap] using h

end PoincareConjecture.RicciFlow.Splitting
