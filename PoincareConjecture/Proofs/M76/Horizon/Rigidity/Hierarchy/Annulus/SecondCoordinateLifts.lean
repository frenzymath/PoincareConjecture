import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedCircleLifts
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetTranslation
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood










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


noncomputable def hamiltonZeroSecondCircleMap (phi : C(H0, H0)) : C(X0, C0) :=
  ⟨fun x => (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).1.2,
    (hamiltonZeroHierarchyCoordinates.continuous.comp
      (phi.continuous.comp hamiltonZeroAmbientEquiv.continuous)).fst.snd⟩

theorem hamiltonZeroSecondCircleMap_ambient (phi : C(H0, H0)) (x : X0) :
    hamiltonZeroSecondCircleMap phi x =
      ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
        (hamiltonZeroAmbientMap phi x)).1.2 := by
  change _ = (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv
    (hamiltonZeroAmbientEquiv.symm (phi (hamiltonZeroAmbientEquiv x))))).1.2
  rw [hamiltonZeroAmbientEquiv.apply_symm_apply]
  rfl

theorem hamiltonZeroSecondCircleMap_domain (phi : C(H0, H0)) (x : R0) :
    hamiltonZeroSecondCircleMap phi (x : X0) =
      (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi x : X0))).1.2 := by
  let q := latticeHandleDomainEquiv (Fin 0) (Fin 3) L0
  change (hamiltonZeroHierarchyCoordinates (phi (hamiltonZeroAmbientEquiv x))).1.2 = _
  rw [hamiltonZeroAmbientEquiv_domain, hamiltonZeroAmbientEquiv_domain]
  change (hamiltonZeroHierarchyCoordinates (phi (q x))).1.2 =
    (hamiltonZeroHierarchyCoordinates (q (q.symm (phi (q x))))).1.2
  rw [q.apply_symm_apply]



theorem exists_hamiltonZeroSecondCircleMap_lift {ι κ : Type*}
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
        hamiltonZeroSecondCircleMap phi ((e i).symm z) = (w z : C0) := by
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
    ((ContinuousLinearMap.proj (1 : Fin 3) : V3 →L[ℝ] ℝ).comp
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
    change hamiltonZeroSecondCircleMap phi (y : X0) = ((lam (F z) : ℝ) : C0)
    rw [hamiltonZeroSecondCircleMap_domain, hactual]
    rfl



theorem exists_hamiltonZeroSecondCircleMap_lift_in_compatible_chart {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (x : X0) (G : OpenPartialHomeomorph X0 V3)
    (hG : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3)
    (hxG : x ∈ G.source) :
    ∃ (K : SimplicialComplex ℝ V3) (w : V3 → ℝ),
      K.faces.Finite ∧ G x ∈ interior K.space ∧ K.space ⊆ G.target ∧
      K.AffineOnFaces w ∧
      ∀ y ∈ G.source, G y ∈ K.space → hamiltonZeroSecondCircleMap phi y = (w (G y) : C0) := by
  obtain ⟨i, K, w, hK, hxi, hxK, _, hw, hlift⟩ :=
    exists_hamiltonZeroSecondCircleMap_lift e d hd phi hphi x
  let Q := G.symm.trans (e i)
  have hQ : LocallyPiecewiseAffineOn Q Q.source := by
    have hinv := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (hG i)).2
    change LocallyPiecewiseAffineOn ((e i).symm.trans G).symm
      ((e i).symm.trans G).symm.source at hinv
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using hinv
  have hwlocal : LocallyPiecewiseAffineOn w (interior K.space) :=
    (hw.finitePiecewiseAffineOn hK).locallyPiecewiseAffineOn_of_subset_interior
      isOpen_interior (Subset.refl _)
  have hxQ : G x ∈ Q.source ∩ Q ⁻¹' interior K.space := by
    refine ⟨⟨G.map_source hxG, ?_⟩, ?_⟩
    · change G.symm (G x) ∈ (e i).source
      rwa [G.left_inv hxG]
    · change e i (G.symm (G x)) ∈ interior K.space
      rwa [G.left_inv hxG]
  obtain ⟨J, hJ, hxJ, hJU, hfJ⟩ := (hwlocal.comp hQ) (G x) hxQ
  refine ⟨J, w ∘ Q, hJ, hxJ, fun z hz => (hJU hz).1.1, hfJ, ?_⟩
  intro y hyG hyJ
  have hyi : y ∈ (e i).source := by
    have h := (hJU hyJ).1.2
    change G.symm (G y) ∈ (e i).source at h
    rwa [G.left_inv hyG] at h
  have hyK : e i y ∈ K.space := by
    have h := interior_subset (hJU hyJ).2
    change e i (G.symm (G y)) ∈ K.space at h
    rwa [G.left_inv hyG] at h
  have h := hlift (e i y) hyK
  rw [(e i).left_inv hyi] at h
  change hamiltonZeroSecondCircleMap phi y = (w (e i (G.symm (G y))) : C0)
  rwa [G.left_inv hyG]

end PoincareConjecture.M76
