import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.SourcePhaseCharts










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus



theorem finitePiecewiseAffineOn_of_circle_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (p : ℝ) [Fact (0 < p)] (f w : E → ℝ)
    (hf : ContinuousOn f K.space) (hw : FinitePiecewiseAffineOn w K.space)
    (heq : ∀ x ∈ K.space, (f x : AddCircle p) = (w x : AddCircle p)) :
    FinitePiecewiseAffineOn f K.space := by
  classical
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  let delta := f x - w x
  let W : Set K.space := {y | f y - w y ∈ Ioo (delta - p / 2) (delta + p / 2)}
  have hc : Continuous (fun y : K.space => f y - w y) :=
    (hf.sub hw.continuousOn).comp_continuous continuous_subtype_val (fun y => y.property)
  have hW : IsOpen W := isOpen_Ioo.preimage hc
  have hp : 0 < p := Fact.out
  have hxW : x ∈ W := by change delta - p / 2 < delta ∧ delta < delta + p / 2; constructor <;> linarith
  obtain ⟨J, V, hJ, hJK, hV, hxV, hVJ, hJW⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hW hxW
  have hconstant (y : E) (hy : y ∈ J.space) : f y - w y = delta := by
    have hyW : (⟨y, hJK hy⟩ : K.space) ∈ W := hJW hy
    have hmod (z : E) (hz : z ∈ K.space) : ((f z - w z : ℝ) : AddCircle p) = 0 := by
      rw [AddCircle.coe_sub, heq z hz, sub_self]
    have hyI : f y - w y ∈ Ico (delta - p / 2) (delta - p / 2 + p) :=
      ⟨hyW.1.le, by linarith [hyW.2]⟩
    have hxI : delta ∈ Ico (delta - p / 2) (delta - p / 2 + p) := by
      constructor <;> linarith
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hyI hxI).mp
      ((hmod y (hJK hy)).trans (hmod x x.property).symm)
  let addDelta : ℝ →ᴬ[ℝ] ℝ :=
    ContinuousAffineMap.id ℝ ℝ + ContinuousAffineMap.const ℝ ℝ delta
  have hlocal := (hw.restrict J hJ hJK).postcomp addDelta
  have hlocalf : FinitePiecewiseAffineOn f J.space := hlocal.congr (by
    intro y hy
    change w y + delta = f y
    linarith [hconstant y hy])
  obtain ⟨Q, hQ, hQJ, hfQ⟩ := hlocalf
  exact ⟨Q, V, hQ, hV, hxV, fun y hy => hQJ.symm.subset (hVJ hy), hfQ⟩

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p




theorem finitePiecewiseAffineOn_sourcePhase_lift
    {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : α → OpenPartialHomeomorph X V3) (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → R)
    (hf : PolyhedralPLInCharts e (fun z => (f z : X)) K.space)
    (w : E → ℝ) (hw : ContinuousOn w K.space)
    (hlift : ∀ z ∈ K.space, (w z : C) =
      sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L (f z))) :
    FinitePiecewiseAffineOn w K.space := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, J, V, hJ, hJK, hV, hxV, hVJ, hfJ, hcoords⟩ := hf.coordinates x
  have hxJ : (x : E) ∈ J.space := hVJ ⟨x, hxV, rfl⟩
  obtain ⟨Kc, u, hKc, hxKc, _, hu, hphase⟩ :=
    exists_sourcePhase_lift_in_compatible_chart e d hd phi hphi (f x) (e i)
      (fun j => hphi.source_domain.compatible j i) (hfJ hxJ)
  let W : Set X := (e i).source ∩ (e i) ⁻¹' interior Kc.space
  have hW : IsOpen W := (e i).continuousOn.isOpen_inter_preimage
    (e i).open_source isOpen_interior
  let O : Set K.space := V ∩ (fun z : K.space => (f z : X)) ⁻¹' W
  have hO : IsOpen O := hV.inter (hW.preimage
    (hf.continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)))
  have hxO : x ∈ O := ⟨hxV, hfJ hxJ, hxKc⟩
  obtain ⟨Q, U, hQ, hQK, hU, hxU, hUQ, hQO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO hxO
  have hQJ : Q.space ⊆ J.space := fun y hy =>
    hVJ ⟨⟨y, hQK hy⟩, (hQO hy).1, rfl⟩
  have huc : FinitePiecewiseAffineOn (fun z => u (e i (f z))) Q.space :=
    (hu.finitePiecewiseAffineOn hKc).comp (hcoords.restrict Q hQ hQJ)
      (fun y hy => interior_subset (hQO (a := ⟨y, hQK hy⟩) hy).2.2)
  have hwQ := finitePiecewiseAffineOn_of_circle_lift Q hQ p w
    (fun z => u (e i (f z))) (hw.mono hQK) huc (by
      intro y hy
      exact (hlift y (hQK hy)).trans
        (hphase (f y) (hQO (a := ⟨y, hQK hy⟩) hy).2.1
          (interior_subset (hQO (a := ⟨y, hQK hy⟩) hy).2.2)))
  obtain ⟨T, hT, hTQ, hwT⟩ := hwQ
  exact ⟨T, U, hT, hU, hxU, fun y hy => hTQ.symm.subset (hUQ hy), hwT⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
