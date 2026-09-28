import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.HausdorffDistance












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold

namespace PoincareConjecture



theorem m64ClosedEmbedding_continuous_representative
    {m : ℕ} {M : Type*} [TopologicalSpace M]
    {e : M → EuclideanSpace ℝ (Fin m)} (hei : IsClosedEmbedding e)
    {O : Set LoopPlane} (hO : IsOpen O)
    (f : LoopPlane → M) (U : LoopPlane → EuclideanSpace ℝ (Fin m))
    (hU : ContinuousOn U O) (hae : U =ᵐ[volume.restrict O] (e ∘ f)) :
    ∃ F : LoopPlane → M, ContinuousOn F O ∧
      F =ᵐ[volume.restrict O] f ∧ EqOn (e ∘ F) U O := by
  classical
  have htarget : MapsTo U O (range e) := by
    have hd : ContinuousOn (fun p => Metric.infDist (U p) (range e)) O :=
      (Metric.continuous_infDist_pt (range e)).comp_continuousOn hU
    have hz : (fun p => Metric.infDist (U p) (range e)) =ᵐ[volume.restrict O]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hae] with p hp
      rw [hp]
      exact Metric.infDist_zero_of_mem (mem_range_self (f p))
    have hclosure : O ⊆ closure (interior O) := by
      rw [hO.interior_eq]
      exact subset_closure
    have hzero := Measure.eqOn_of_ae_eq hz hd continuousOn_const hclosure
    intro p hp
    exact (hei.isClosed_range.mem_iff_infDist_zero ⟨e (f 0), mem_range_self _⟩).mpr (hzero hp)
  let F : LoopPlane → M := fun p => if h : U p ∈ range e then Classical.choose h else f 0
  have hFe (p : LoopPlane) (hp : p ∈ O) : e (F p) = U p := by
    simp only [F, dif_pos (htarget hp)]
    exact Classical.choose_spec (htarget hp)
  refine ⟨F, hei.isEmbedding.continuousOn_iff.mpr (hU.congr hFe), ?_, hFe⟩
  filter_upwards [hae, ae_restrict_mem hO.measurableSet] with p hp hpO
  exact hei.isEmbedding.injective ((hFe p hpO).trans hp)

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem M64ObservedWeakAnnulus.with_map_ae
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (f : LoopPlane → M) (hf : f =ᵐ[mu] A.map) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      B.map = f ∧ B.column = A.column ∧
      ∀ Q : M → E →L[ℝ] E →L[ℝ] ℝ, B.energy Q = A.energy Q := by
  have hobs : (e ∘ f) =ᵐ[mu] (e ∘ A.map) := hf.fun_comp e
  have hint (phi : LoopPlane → ℝ) :
      (∫ p in S, phi p • e (f p)) = ∫ p in S, phi p • e (A.map p) :=
    integral_congr_ae (hf.mono fun p hp => congrArg (fun q => phi p • e q) hp)
  let B : M64ObservedWeakAnnulus (n := n) e c0 c1 := {
    map := f
    observed_memLp := A.observed_memLp.ae_eq hobs.symm
    column := A.column
    tangent := fun i => by
      filter_upwards [hf, A.tangent i] with p hp ht
      rw [hp]
      exact ht
    weak_partial := fun i b => m64WeakPartialDeriv_ae_congr
      (hobs.symm.mono fun p hp => congrArg (fun v : E => v b) hp)
      EventuallyEq.rfl (A.weak_partial i b)
    boundary := fun phi hphi => by rw [hint]; exact A.boundary phi hphi
    seam := fun phi hphi hseam => by rw [hint]; exact A.seam phi hphi hseam }
  refine ⟨B, rfl, rfl, ?_⟩
  intro Q
  apply integral_congr_ae
  filter_upwards [hf] with p hp
  change (Q (f p) (A.column 0 p) (A.column 0 p) +
    Q (f p) (A.column 1 p) (A.column 1 p)) / 2 = _
  rw [hp]

end PoincareConjecture
