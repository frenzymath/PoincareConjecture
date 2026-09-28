import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TensorCone
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.RicciComplementEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.GeometricPreservation.Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle Filter
open PoincareConjecture.RicciFlow.Frame
open scoped Manifold ContDiff Topology InnerProductSpace Classical

namespace PoincareConjecture.AncientKappaRoundness

private theorem continuousOn_of_tensor_components
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ E) {k : ℕ}
    {T : X → TensorFiber E k} {S : Set X}
    (h : ∀ v : Fin k → ι, ContinuousOn (fun x => T x (fun i => e (v i))) S) :
    ContinuousOn T S := by
  let C : TensorFiber E k →ₗ[ℝ] ((Fin k → ι) → ℝ) :=
    { toFun := fun R v => R (fun i => e (v i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hC : Function.Injective C := by
    intro A B heq
    apply TensorFiber.toMultilinear.injective
    apply Module.Basis.ext_multilinear (fun _ => e)
    intro v
    exact congrFun heq v
  obtain ⟨L, hL⟩ := C.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  have hLC (R : TensorFiber E k) : L (C R) = R :=
    congrArg (fun f : TensorFiber E k →ₗ[ℝ] TensorFiber E k => f R) hL
  have hc : ContinuousOn (fun x => C (T x)) S := continuousOn_pi.mpr h
  have hd := L.toContinuousLinearMap.continuous.comp_continuousOn hc
  change ContinuousOn (fun x => L (C (T x))) S at hd
  simpa only [hLC] using hd

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

theorem exists_transportedRicciComplement_local_coordinates
    (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (Ico a b ×ˢ univ))
    (c : ℝ) {d : ℝ} (hd : d < b) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∃ (O : M → Set M), (∀ p, IsOpen (O p)) ∧ (∀ p, p ∈ O p) ∧
      ∃ e : ∀ p x, x ∈ O p →
          TensorFiber (TangentSpace (𝓡 3) p) 2 ≃ₗᵢ[ℝ]
            TensorFiber (TangentSpace (𝓡 3) x) 2,
        (∀ p x hx, e p x hx '' tensorPinchingCone c = tensorPinchingCone c) ∧
        ∀ p, ContinuousOn (fun z : M × ℝ =>
          if hx : z.1 ∈ O p then
            (e p z.1 hx).symm (transportedRicciComplement F hcalculus z.2 z.1)
          else 0) (O p ×ˢ Icc a d) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  choose r Y hr hrU hY hinit hpar P hP using
    fun p : M => (F.connection a).exists_radialParallelIsometries_with_fields p
  let O (p : M) := LeviCivitaData.radialNeighborhood (n := 3) p (r p)
  let e (p x : M) (hx : x ∈ O p) := TensorFiber.transport (P p ⟨x, hx⟩) 2
  refine ⟨O, fun p => LeviCivitaData.isOpen_radialNeighborhood p (r p),
    fun p => LeviCivitaData.mem_radialNeighborhood p (hr p), e, ?_, ?_⟩
  · intro p x hx
    exact tensorPinchingCone_transport_image (P p ⟨x, hx⟩) c
  · intro p
    apply continuousOn_of_tensor_components (stdOrthonormalBasis ℝ
      (TangentSpace (𝓡 3) p)).toBasis
    intro v
    let W (i : Fin 2) (x : M) := LeviCivitaData.fieldFromCenteredCoordinates p
      (Y p (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p) (v i))) x
    have hW (i : Fin 2) (x : M) (hx : x ∈ O p) :
        ContMDiffAt (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% (W i)) x :=
      LeviCivitaData.contMDiffAt_fieldFromCenteredCoordinates p
        (hY p _).contDiffAt hx.1
    let Z (i : Fin 2) (z : ℝ × M) := canonicalTransport F z.1 z.2 (W i z.2)
    have hZ (i : Fin 2) (z : ℝ × M) (hz : z ∈ Ico a b ×ˢ O p) :
        ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 3)) ((𝓡 3).prod (𝓡 3)) ∞
          (fun z => TotalSpace.mk' (EuclideanSpace ℝ (Fin 3)) z.2 (Z i z))
          (Ico a b ×ˢ O p) z := by
      have htr := ((canonicalTransport_contMDiffOn F) z ⟨hz.1, trivial⟩).mono
        (prod_mono Subset.rfl (subset_univ (O p)))
      exact htr.clm_bundle_apply
        (((hW i z.2 hz.2).comp z contMDiffAt_snd).contMDiffWithinAt)
    have hcoeff : ContinuousOn (fun z : ℝ × M =>
        (F.connection z.1).ricciComplementEvaluation z.2 ![Z 0 z, Z 1 z])
        (Ico a b ×ˢ O p) := by
      intro z hz
      have hsub : Ico a b ×ˢ O p ⊆ Ico a b ×ˢ (univ : Set M) :=
        prod_mono Subset.rfl (subset_univ (O p))
      have hR := (hscalar z ⟨hz.1, trivial⟩).mono hsub
      have hG := (F.smooth z ⟨hz.1, trivial⟩).mono hsub
      have hpair := (contMDiffWithinAt_totalSpace.mp
        (hG.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := fun _ : M => ℝ)
          (hZ 0 z hz) (hZ 1 z hz))).2
      exact (((hR.div_const 2).mul hpair).sub
        (contMDiffWithinAt_ricci_spacetime_fields F hz.1 hz.2
          (Z 0) (Z 1) (hZ 0 z hz) (hZ 1 z hz))).continuousWithinAt
    have hswap := hcoeff.comp continuous_swap.continuousOn
      (show MapsTo Prod.swap (O p ×ˢ Icc a d) (Ico a b ×ˢ O p) from
        fun z hz => ⟨⟨hz.2.1, hz.2.2.trans_lt hd⟩, hz.1⟩)
    apply hswap.congr
    intro z hz
    dsimp only
    rw [dif_pos hz.1]
    change transportedRicciComplement F hcalculus z.2 z.1
      (fun i => P p ⟨z.1, hz.1⟩ (stdOrthonormalBasis ℝ
        (TangentSpace (𝓡 3) p) (v i))) = _
    simp only [transportedRicciComplement_apply, hP]
    congr 2
    ext i
    fin_cases i <;> rfl

end PoincareConjecture.AncientKappaRoundness
