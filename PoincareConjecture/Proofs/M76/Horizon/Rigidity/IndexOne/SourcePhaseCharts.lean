import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.SourcePhase
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))



theorem exists_sourcePhase_lift_in_compatible_chart
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (x : R) (G : OpenPartialHomeomorph X V3)
    (hG : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3)
    (hxG : (x : X) ∈ G.source) :
    ∃ (K : SimplicialComplex ℝ V3) (w : V3 → ℝ),
      K.faces.Finite ∧ G x ∈ interior K.space ∧ K.space ⊆ G.target ∧
      K.AffineOnFaces w ∧
      ∀ (y : R), (y : X) ∈ G.source → G y ∈ K.space →
        sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L y) =
          (w (G y) : C) := by
  obtain ⟨i, K, V, w, hK, hV, hxV, hVi, hVK, hKt, hKR, hw, hlift⟩ :=
    exists_sourcePhase_finite_lift e d hd phi hphi x
  obtain ⟨g, T, hT, hKT, hg, hgw⟩ :=
    (hw.finitePiecewiseAffineOn hK).exists_locallyPiecewiseAffine_extension
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  have hxO : (x : X) ∈ O := by
    change x ∈ (Subtype.val : R → X) ⁻¹' O
    rwa [hOV]
  let Q := G.symm.trans (e i)
  have hQ : LocallyPiecewiseAffineOn Q Q.source := by
    have hinv := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (hG i)).2
    change LocallyPiecewiseAffineOn ((e i).symm.trans G).symm
      ((e i).symm.trans G).symm.source at hinv
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm] using hinv
  let U := (Q.source ∩ Q ⁻¹' T) ∩ (G.target ∩ G.symm ⁻¹' O)
  have hU : IsOpen U :=
    (Q.continuousOn.isOpen_inter_preimage Q.open_source hT).inter
      (G.isOpen_inter_preimage_symm hO)
  have hxU : G x ∈ U := by
    have hxi := hVi hxV
    have hxK := hVK ⟨x, hxV, rfl⟩
    refine ⟨⟨⟨G.map_source hxG, ?_⟩, ?_⟩, G.map_source hxG, ?_⟩
    · change G.symm (G x) ∈ (e i).source
      rwa [G.left_inv hxG]
    · change e i (G.symm (G x)) ∈ T
      rw [G.left_inv hxG]
      exact hKT hxK
    · change G.symm (G x) ∈ O
      rwa [G.left_inv hxG]
  have hlocal : LocallyPiecewiseAffineOn (g ∘ Q) U :=
    (hg.comp hQ).mono hU inter_subset_left
  obtain ⟨J, hJ, hxJ, hJU, hfJ⟩ := hlocal (G x) hxU
  refine ⟨J, g ∘ Q, hJ, hxJ, fun z hz => (hJU hz).2.1, hfJ, ?_⟩
  intro y hyG hyJ
  have hyU := hJU hyJ
  have hyO : (y : X) ∈ O := by
    have h := hyU.2.2
    change G.symm (G y) ∈ O at h
    rwa [G.left_inv hyG] at h
  have hyV : y ∈ V := by rw [← hOV]; exact hyO
  have hyi := hVi hyV
  have hyK : e i y ∈ K.space := hVK ⟨y, hyV, rfl⟩
  have hval := hlift (e i y) hyK (by rw [(e i).left_inv hyi]; exact y.property)
  have hysub : (⟨(e i).symm (e i y), by rw [(e i).left_inv hyi]; exact y.property⟩ : R) = y :=
    Subtype.ext ((e i).left_inv hyi)
  rw [hysub] at hval
  change sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L y) =
    (g (e i (G.symm (G y))) : C)
  rw [G.left_inv hyG, hgw hyK]
  exact hval

end PoincareConjecture.M76.HamiltonIntervalTorus
