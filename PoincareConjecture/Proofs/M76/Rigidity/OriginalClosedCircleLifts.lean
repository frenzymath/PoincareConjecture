import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleMap
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V0" => (Fin 0 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

theorem exists_hamiltonZeroCircleMap_lift {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (x : X0) :
    ∃ (i : ι) (K : SimplicialComplex ℝ V3) (w : V3 → ℝ),
      K.faces.Finite ∧ x ∈ (e i).source ∧
      e i x ∈ interior K.space ∧ K.space ⊆ (e i).target ∧
      K.AffineOnFaces w ∧
      ∀ z ∈ K.space,
        hamiltonZeroCircleMap phi ((e i).symm z) = (w z : C0) := by
  let xR : R0 := ⟨x, by rw [hamiltonZeroDomain_eq_univ]; trivial⟩
  obtain ⟨i, j, K, V, F, _, hV, hxV, _, hVi, hVK, hKt, _, hF, hformula⟩ :=
    hphi.coordinates xR (mem_univ xR)
  have hRopen : IsOpen R0 := by rw [hamiltonZeroDomain_eq_univ]; exact isOpen_univ
  let U : Set X0 := (Subtype.val : R0 → X0) '' V
  have hU : IsOpen U := hRopen.isOpenMap_subtype_val V hV
  have hUsource : U ⊆ (e i).source := by
    rintro y ⟨z, hz, rfl⟩
    exact hVi hz
  have hUK : (e i) '' U ⊆ K.space := by
    rintro z ⟨y, ⟨yR, hyR, rfl⟩, rfl⟩
    exact hVK ⟨yR, hyR, rfl⟩
  have hximage : e i x ∈ (e i) '' U := ⟨x, ⟨xR, hxV, rfl⟩, rfl⟩
  have hxK : e i x ∈ interior K.space :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset
        (((e i).isOpen_image_of_subset_source hU hUsource).mem_nhds hximage) hUK)
  obtain ⟨a, ha⟩ := hd.inverse_formula j
  let lam : V3 →ᴬ[ℝ] ℝ :=
    ((ContinuousLinearMap.proj (2 : Fin 3) : V3 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ V0 V3)).toContinuousAffineMap.comp
        a.toContinuousAffineMap
  obtain ⟨J, hJ, hJK, hw⟩ := hF.postcomp lam
  refine ⟨i, J, lam ∘ F, hJ, hVi hxV, ?_, ?_, hw, ?_⟩
  · simpa only [hJK] using hxK
  · exact hJK.subset.trans hKt
  · intro z hz
    have hzK : z ∈ K.space := hJK.subset hz
    let y : R0 := ⟨(e i).symm z, by rw [hamiltonZeroDomain_eq_univ]; trivial⟩
    have hyi : (y : X0) ∈ (e i).source := (e i).map_target (hKt hzK)
    have hiy : e i (y : X0) = z := (e i).right_inv (hKt hzK)
    obtain ⟨hys, heq⟩ := hformula y hyi (by simpa only [hiy] using hzK)
    rw [hiy] at heq
    have hFt : F z ∈ (d j).target := heq.symm ▸ (d j).map_source hys
    have hactual :
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi y : X0) =
          ((a (F z)).1, QuotientAddGroup.mk (a (F z)).2) := by
      calc
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi y : X0) =
            (d j).symm (d j (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi y)) :=
          ((d j).left_inv hys).symm
        _ = (d j).symm (F z) := congrArg (d j).symm heq.symm
        _ = ((a (F z)).1, QuotientAddGroup.mk (a (F z)).2) := ha (F z) hFt
    change hamiltonZeroCircleMap phi (y : X0) = ((lam (F z) : ℝ) : C0)
    rw [hamiltonZeroCircleMap_domain, hactual, hamiltonZeroAmbientCircle_mk]
    rfl

end PoincareConjecture.M76
