import PoincareConjecture.Proofs.M34.Mathlib.EvenSphereStrip
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderDifferential
import PoincareConjecture.Definitions.M27ProductModels
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M34

section Cover

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem projectivePlaneLine_cover_not_immersed
    {K : AncientKappaSolution 3 M} (P : M27ProjectivePlaneLineFlowCertificate K)
    {U : Set M} (hU : IsOpen U)
    (hcover : P.cover '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ U)
    (f : M → EuclideanSpace ℝ (Fin 3)) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinj : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x)) : False := by
  have hmaps : MapsTo P.cover (univ ×ˢ Ioo (-1 : ℝ) 1) U := by
    intro p hp
    exact hcover ⟨p, ⟨hp.1, hp.2.1.le, hp.2.2.le⟩, rfl⟩
  have hc := P.cover_local_diffeomorph.contMDiff
  have hH : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (f ∘ P.cover)
      (univ ×ˢ Ioo (-1 : ℝ) 1) :=
    hf.comp hc.contMDiffOn hmaps
  have hHi (p : UnitTwoSphere × ℝ) (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      Function.Injective
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (f ∘ P.cover) p) := by
    have hdf := ((hf (P.cover p) (hmaps hp)).contMDiffAt
      (hU.mem_nhds (hmaps hp))).mdifferentiableAt (by simp)
    rw [mfderiv_comp p hdf (hc.mdifferentiable (by simp) p)]
    exact (hinj (P.cover p) (hmaps hp)).comp
      ((P.cover_local_diffeomorph.mfderivToContinuousLinearEquiv (by simp) p).injective)
  have heven (p : UnitTwoSphere × ℝ) (_hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      (f ∘ P.cover) (-p.1, p.2) = (f ∘ P.cover) p := by
    exact congrArg f ((P.cover_fibers p (-p.1, p.2)).mpr (Or.inr rfl)).symm
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hdim : Odd (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
    rw [finrank_euclideanSpace_fin]
    decide
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact not_even_sphere_strip_immersion (n := 2) (f ∘ P.cover) (hH.of_le (by simp)) hHi heven
    (isPreconnected_sphere hrank 0 1) hdim
    ((EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one 0)

end Cover

section Convergence

variable {S : GeneralizedBlowupSequence.{u}}
  (C : GeneralizedBlowupConvergence S (blowupBackwardInterval ⊤))

local instance : TopologicalSpace C.limit.carrier.carrier := C.limit.carrier.topologicalSpace
local instance : MeasurableSpace C.limit.carrier.carrier := C.limit.carrier.measurableSpace
local instance : BorelSpace C.limit.carrier.carrier := C.limit.carrier.borelSpace
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold
local instance : T2Space C.limit.carrier.carrier := C.limit.carrier.t2Space
local instance : T3Space C.limit.carrier.carrier := C.limit.carrier.t3Space
local instance : SecondCountableTopology C.limit.carrier.carrier :=
  C.limit.carrier.secondCountable
local instance : ConnectedSpace C.limit.carrier.carrier := C.limit.connectedSpace

theorem generalizedBlowupConvergence_not_projectivePlaneLine
    {kappa : ℝ} (A : BlowupAncientKappaIdentification C.limit kappa)
    (hsource : ∀ k t, t ∈ (S.flow k).interval →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3)
        ((S.flow k).slice t).carrier (EuclideanSpace ℝ (Fin 3)) ∞)) :
    ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate A.solution) := by
  rintro ⟨P⟩
  have hcompact : IsCompact (P.cover '' (univ ×ˢ Icc (-1 : ℝ) 1)) :=
    (isCompact_univ.prod isCompact_Icc).image P.cover_local_diffeomorph.contMDiff.continuous
  obtain ⟨k, hk⟩ := hcompact.elim_directed_cover C.exhaustion.space
    C.exhaustion.space_open
    (fun x _ => C.exhaustion.space_covers.symm ▸ mem_univ x)
    C.exhaustion.space_increasing.directed_le
  have hzero : 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  let e := C.embedding k
  have ht : (S.base (C.subsequence k)).1 + 0 / S.scale (C.subsequence k) ∈
      (S.flow (C.subsequence k)).interval :=
    ((S.flow (C.subsequence k)).slice_nonempty_iff _).mp
      ⟨e.forward 0 hzero C.limit.base⟩
  obtain ⟨psi⟩ := hsource (C.subsequence k) _ ht
  let f := psi ∘ e.forward 0 hzero
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (C.exhaustion.space k) :=
    psi.contMDiff.comp_contMDiffOn (e.forward_smooth 0 hzero)
  have hinj (x : C.limit.sliceCarrier.carrier) (hx : x ∈ C.exhaustion.space k) :
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x) := by
    have he := ((e.forward_smooth 0 hzero x hx).contMDiffAt
      ((C.exhaustion.space_open k).mem_nhds hx)).mdifferentiableAt (by simp)
    change Function.Injective (mfderiv (𝓡 3) (𝓡 3) (psi ∘ e.forward 0 hzero) x)
    rw [mfderiv_comp x (psi.mdifferentiable (by simp) _) he]
    exact (psi.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (e.forward_mfderiv_injective (C.exhaustion.space_open k) hzero hx)
  exact projectivePlaneLine_cover_not_immersed P (C.exhaustion.space_open k) hk f hf hinj

end Convergence

end PoincareConjecture.M34
