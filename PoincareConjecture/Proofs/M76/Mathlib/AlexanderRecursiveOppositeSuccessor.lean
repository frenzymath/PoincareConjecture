import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOppositeSide
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedCover
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBaseRestriction
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem AlexanderCollarSlab.nonempty_opposite_pointed_successor
    {S s s' b d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hqs : q ∈ s)
    (N Ks : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    (hB : S ∩ {x | A x = 0} = b ∪ N.space) (htouch : b ∩ N.space ⊆ {q})
    (hother : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → ((M.chart p : E) ∈ s ↔ (p : E × ℝ).2 = 0))
    (hd : d ⊆ {x | A x = 0}) (H : E ≃ₜ E)
    (hdecrease : ∀ x, A (H x) ≤ A x)
    (hfix : ∀ x ∈ s, 0 < A x → H x = x)
    (hzero : (H '' (s ∪ d)) ∩ {x | A x = 0} = (N.space ∩ s) ∪ {q}) :
    Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) := by
  classical
  let X : Set E := (N.space ∩ s) ∪ {q}
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have hbzero : b ⊆ {x | A x = 0} :=
    (subset_union_left.trans hB.symm.subset).trans inter_subset_right
  have hkB : N.space ⊆ S ∩ {x | A x = 0} := subset_union_right.trans hB.symm.subset
  have hXB : X ⊆ S ∩ {x | A x = 0} := by
    rintro x (hx | hx)
    · exact hkB hx.1
    · exact (mem_singleton_iff.mp hx).symm ▸ And.intro M.apex_mem M.apex_height
  have hqX : q ∈ X := Or.inr rfl
  obtain ⟨J₀, hJ₀, hJ₀s⟩ := N.exists_finite_triangulation_inter Ks hN hKs
  rw [hKss] at hJ₀s
  obtain ⟨Jq, hJq, hJqs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
    (fun _ : Unit => ({q} : Finset E)) (fun _ => affineIndependent_of_subsingleton ℝ _)
  have hJqspace : Jq.space = {q} := by simpa using hJqs
  obtain ⟨KX, hKX, hKXs⟩ := J₀.exists_finite_triangulation_union Jq hJ₀ hJq
  rw [hJ₀s, hJqspace] at hKXs
  obtain ⟨TX, hTX, C, hC, hCval, hCX⟩ :=
    M.chart_finitePL.exists_collar_base_restriction M.width_pos
      (fun x hx => (M.upper_bounds x hx).2) hXB KX hKX hKXs
  have hT : M.collar ⊆ S ∩ {x | A x ∈ Icc 0 β} :=
    subset_union_left.trans M.cover.subset
  have hR : M.residual ⊆ S ∩ {x | A x ∈ Icc 0 β} :=
    subset_union_right.trans M.cover.subset
  have hfiber := M.chart.collar_fiber_mem_cut_iff M.height M.bottom hs hs'
    ((hT.trans inter_subset_left).trans hunion.symm.subset) hinter hbzero
  have hTXs : TX ⊆ s := by
    intro x hx
    let p := M.chart.symm ⟨x, hTX hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    rcases (hCX p).mp (hp.symm ▸ hx) with hxk | hxq
    · by_cases hpb : (p : E × ℝ).1 ∈ b
      · have hpq : (p : E × ℝ).1 = q := htouch ⟨hpb, hxk.1⟩
        have hxq : x = q := hp.symm.trans (M.chart_eq_apex_of_base_eq p hpq)
        exact hxq.symm ▸ hqs
      · exact hp ▸ (hfiber p hpb).1.mpr hxk.2
    · have hxq' : x = q := hp.symm.trans (M.chart_eq_apex_of_base_eq p hxq)
      exact hxq'.symm ▸ hqs
  have hXTX : X ⊆ TX := by
    intro x hx
    let p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)} :=
      ⟨(x, 0), hx, le_rfl, (M.upper_bounds x (hXB hx)).1⟩
    have hp : (C p : E) = x := (hCval p).trans (M.bottom _ rfl)
    have hmem : (C p : E) ∈ TX := (C p).property
    rwa [hp] at hmem
  have hTXzero : TX ∩ {x | A x = 0} ⊆ X :=
    M.restricted_collar_zero_subset hTX (fun p hp => (hCX p).mp hp)
  have hpositiveTX (x : E) (hxT : x ∈ M.collar) (hxs : x ∈ s)
      (hxA : 0 < A x) : x ∈ TX := by
    let p := M.chart.symm ⟨x, hxT⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    have hpb : (p : E × ℝ).1 ∉ b := by
      intro hpb
      have hpzero := (hother p hpb).mp (hp.symm ▸ hxs)
      have hxzero : A x = 0 := (congrArg A hp).symm.trans ((M.height p).trans hpzero)
      exact hxA.ne' hxzero
    have hpk : (p : E × ℝ).1 ∈ N.space := (hB.subset p.property.1).resolve_left hpb
    have hps : (p : E × ℝ).1 ∈ s := (hfiber p hpb).1.mp (hp.symm ▸ hxs)
    exact hp ▸ (hCX p).mpr (Or.inl ⟨hpk, hps⟩)
  have hnewpos (x : E) (hxA : 0 < A x) : x ∈ H '' (s ∪ d) ↔ x ∈ s := by
    constructor
    · rintro ⟨y, hys | hyd, hyx⟩
      · have hbound := hdecrease y
        rw [hyx] at hbound
        have hypos : 0 < A y := hxA.trans_le hbound
        have hyx' : y = x := (hfix y hys hypos).symm.trans hyx
        exact hyx' ▸ hys
      · have hbound := hdecrease y
        rw [hyx, show A y = 0 from hd hyd] at hbound
        exact (not_le_of_gt hxA hbound).elim
    · exact fun hxs => ⟨x, Or.inl hxs, hfix x hxs hxA⟩
  have hcover : TX ∪ (M.residual ∩ s) =
      (H '' (s ∪ d)) ∩ {x | A x ∈ Icc 0 β} := by
    ext x
    constructor
    · rintro (hx | hx)
      · have hxband := (hT (hTX hx)).2
        refine ⟨?_, hxband⟩
        by_cases hz : A x = 0
        · exact (hzero.symm.subset (hTXzero ⟨hx, hz⟩)).1
        · exact (hnewpos x (lt_of_le_of_ne hxband.1 (fun h => hz h.symm))).mpr (hTXs hx)
      · have hxband := (hR hx.1).2
        refine ⟨?_, hxband⟩
        by_cases hz : A x = 0
        · have hxq : x = q := M.residual_zero ⟨hx.1, hz⟩
          exact (hzero.symm.subset (Or.inr hxq)).1
        · exact (hnewpos x (lt_of_le_of_ne hxband.1 (fun h => hz h.symm))).mpr hx.2
    · intro hx
      by_cases hz : A x = 0
      · exact Or.inl (hXTX (hzero.subset ⟨hx.1, hz⟩))
      · have hxpos := lt_of_le_of_ne hx.2.1 (fun h => hz h.symm)
        have hxs := (hnewpos x hxpos).mp hx.1
        rcases M.cover.symm.subset ⟨hsS hxs, hx.2⟩ with hxT | hxR
        · exact Or.inl (hpositiveTX x hxT hxs hxpos)
        · exact Or.inr ⟨hxR, hxs⟩
  obtain ⟨J, hJ, hJs⟩ := M.residualComplex.exists_finite_triangulation_inter Ks
    M.residual_finite hKs
  rw [M.residual_space, hKss] at hJs
  have hupperX : FinitePiecewiseAffineOn M.upper X := by
    simpa only [X, hKXs] using
      M.upper_finitePL.restrict KX hKX (hKXs.subset.trans hXB)
  have hdomain : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)} =
      {p : E × ℝ | p.1 ∈ (H '' (s ∪ d)) ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)} := by rw [hzero]
  let D := (Homeomorph.setCongr hdomain.symm).trans (C.trans (Homeomorph.setCongr rfl))
  refine ⟨{
    width_pos := M.width_pos
    apex_mem := (hzero.symm.subset hqX).1
    apex_height := M.apex_height
    upper := M.upper
    collar := TX
    residual := M.residual ∩ s
    residualComplex := J
    chart := D
    chart_finitePL := hC.setCongr hdomain rfl
    residual_finite := hJ
    residual_space := hJs
    cover := hcover
    residual_zero := fun _ hx => M.residual_zero ⟨hx.1.1, hx.2⟩
    roof_contact := ?_
    upper_finitePL := hzero.symm ▸ hupperX
    upper_bounds := fun x hx => M.upper_bounds x (hXB (hzero.subset hx))
    apex_upper := M.apex_upper
    upper_pos := fun x hx => M.upper_pos x (hXB (hzero.subset hx))
    height := ?_
    bottom := ?_
    bottom_covered := hzero.subset.trans hXTX }⟩
  · intro p
    have hval : (D p : E) = M.chart ⟨p,
        hXB (hzero.subset p.property.1), p.property.2⟩ :=
      hCval ⟨p, hdomain.symm ▸ p.property⟩
    have hcontact : (D p : E) ∈ M.residual ↔
        (p : E × ℝ).2 = M.upper (p : E × ℝ).1 := by
      rw [hval]
      exact M.roof_contact _
    constructor
    · exact fun hp => hcontact.mp hp.1
    · exact fun hp => ⟨hcontact.mpr hp, hTXs (D p).property⟩
  · intro p
    change A (C ⟨p, hdomain.symm ▸ p.property⟩) = _
    rw [hCval]
    exact M.height _
  · intro p hp
    change (C ⟨p, hdomain.symm ▸ p.property⟩ : E) = _
    rw [hCval]
    exact M.bottom _ hp

end Geometry
