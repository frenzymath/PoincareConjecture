import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RegularCocoreCrossings

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem ChartwisePLSphere.exists_cocore_innermost_disk_with_crossings_and_presentation
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hJcv : Convex ℝ J.space)
    (H : V3 ≃ᴬ[ℝ] P3) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      (H x).2 ∈ Ioo a b → x ∈ interior J.space) :
    ∃ t ∈ Ioo a b,
      HasDisjointPolygonPresentation
        ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) ∧
      (((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} = ∅) ∨
      ∃ (n : ℕ) (L : Polygon V3 (n + 3)) (D : Set V3),
        Function.Injective L ∧ L.HasSimplicialEdges ∧
        IsFinitePLBallPair P2 D (L.boundary ℝ) ∧
        D ⊆ interior J.space ∩ {x | (H x).2 = t} ∧
        D ∩ Q '' (S ∩ Q.source) = L.boundary ℝ ∧
        IsCompact (((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) \ L.boundary ℝ) ∧
        ∃ U : Set V3, IsOpen U ∧ D ⊆ U ∧ U ⊆ interior J.space ∧
        (∀ x ∈ U, x ∈ L.boundary ℝ ↔ Q.symm x ∈ S ∧ (H x).2 = t) ∧
        ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 P3,
            w ∈ B.source ∧ B.source ⊆ O ∩ interior J.space ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source, (H x).2 - t = (B x).1.1) := by
  let A : V3 →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  obtain ⟨t,ht,hsection,hcrossings⟩ :=
    s.exists_regular_cocore_section_with_crossings Q hQ J hJ hJQ A.toAffineMap hab hband
  change HasDisjointPolygonPresentation
    ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) at hsection
  refine ⟨t,ht,hsection,?_⟩
  by_cases hempty : (Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} = ∅
  · exact Or.inl hempty
  right
  let F : P2 →ᴬ[ℝ] V3 := H.symm.toContinuousAffineMap.comp
    ((ContinuousAffineMap.id ℝ P2).prod (ContinuousAffineMap.const ℝ P2 t))
  let G : V3 →ᴬ[ℝ] P2 :=
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  have hF (z : P2) : F z = H.symm (z,t) := rfl
  have hG (x : V3) : G x = (H x).1 := rfl
  have hleft : Function.LeftInverse G F := by
    intro z
    rw [hG,hF,H.apply_symm_apply]
  have hright : LeftInvOn F G {x | (H x).2 = t} := by
    intro x hx
    rw [hF,hG,← hx]
    exact H.symm_apply_apply x
  have hplane : MapsTo F univ {x | (H x).2 = t} := by
    intro z _
    change (H (F z)).2 = t
    rw [hF,H.apply_symm_apply]
  obtain ⟨n,L,D,hLi,hL,hD,hDsub,hcontact,hremainder⟩ :=
    exists_innermost_disk_in_convex_section_with_polygon hsection hJcv
      (fun x hx => hband x hx.1 (hx.2 ▸ ht)) F G hleft hright hplane
      (Set.nonempty_iff_ne_empty.mpr hempty)
  let C := ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) \ L.boundary ℝ
  let U := interior J.space \ C
  have hU : IsOpen U := isOpen_interior.sdiff hremainder.isClosed
  have hDU : D ⊆ U := by
    intro x hx
    exact ⟨(hDsub hx).1,fun hc => hc.2 (hcontact.subset ⟨hx,hc.1.1.1⟩)⟩
  have hphysical (x : V3) (hx : x ∈ interior J.space) :
      Q.symm x ∈ S ↔ x ∈ Q '' (S ∩ Q.source) := by
    have hxQ := hJQ (interior_subset hx)
    constructor
    · intro h
      exact ⟨Q.symm x,⟨h,Q.map_target hxQ⟩,Q.right_inv hxQ⟩
    · rintro ⟨y,⟨hy,hyQ⟩,hxy⟩
      rw [← hxy,Q.left_inv hyQ]
      exact hy
  refine ⟨n,L,D,hLi,hL,hD,hDsub,hcontact,hremainder,U,hU,hDU,sdiff_subset,?_,?_⟩
  · intro x hx
    constructor
    · intro h
      exact ⟨(hphysical x hx.1).mpr (hcontact.symm.subset h).2,(hDsub (hD.1 h)).2⟩
    · intro h
      by_contra hn
      exact hx.2 ⟨⟨⟨(hphysical x hx.1).mp h.1,interior_subset hx.1⟩,h.2⟩,hn⟩
  · intro w hw O hO hwO
    have hwD := hD.1 hw
    have hwsection : w ∈ (Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} :=
      ⟨⟨(hcontact.symm.subset hw).2,interior_subset (hDsub hwD).1⟩,(hDsub hwD).2⟩
    exact hcrossings w hwsection O hO hwO

theorem ChartwisePLSphere.exists_cocore_innermost_disk_with_crossings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hJcv : Convex ℝ J.space)
    (H : V3 ≃ᴬ[ℝ] P3) {a b : ℝ} (hab : a < b)
    (hband : ∀ x ∈ Q '' (S ∩ Q.source) ∩ J.space,
      (H x).2 ∈ Ioo a b → x ∈ interior J.space) :
    ∃ t ∈ Ioo a b,
      ((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t} = ∅) ∨
      ∃ (n : ℕ) (L : Polygon V3 (n + 3)) (D : Set V3),
        Function.Injective L ∧ L.HasSimplicialEdges ∧
        IsFinitePLBallPair P2 D (L.boundary ℝ) ∧
        D ⊆ interior J.space ∩ {x | (H x).2 = t} ∧
        D ∩ Q '' (S ∩ Q.source) = L.boundary ℝ ∧
        IsCompact (((Q '' (S ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) \ L.boundary ℝ) ∧
        ∃ U : Set V3, IsOpen U ∧ D ⊆ U ∧ U ⊆ interior J.space ∧
        (∀ x ∈ U, x ∈ L.boundary ℝ ↔ Q.symm x ∈ S ∧ (H x).2 = t) ∧
        ∀ w ∈ L.boundary ℝ, ∀ O : Set V3, IsOpen O → w ∈ O →
          ∃ B : OpenPartialHomeomorph V3 P3,
            w ∈ B.source ∧ B.source ⊆ O ∩ interior J.space ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧
            LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source, (H x).2 - t = (B x).1.1 := by
  obtain ⟨t,ht,_,h⟩ :=
    s.exists_cocore_innermost_disk_with_crossings_and_presentation Q hQ J hJ hJQ hJcv H hab hband
  exact ⟨t,ht,h⟩

end PoincareConjecture.M76
