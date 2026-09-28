import PoincareConjecture.Proofs.M25.Topology3D.Polygon.RegionBounds
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcParameter
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcCandidateOrbit
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcCycleSelection
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcTerminalGoodSubarc
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcEarTransfer
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Dist









set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exterior_endpoints_of_internal_vertices {n d : ℕ}
    (p : Polygon E (n + 2)) (X : E →ₗ[ℝ] ℝ)
    (hLR : X (p 0) < X (p (Fin.last (n + 1))))
    (hX : ∀ i, i ≠ 0 → i ≠ Fin.last (n + 1) →
      X (p 0) < X (p i) ∧ X (p i) < X (p (Fin.last (n + 1))))
    (s : Polygon E d) (hd : 0 < d)
    (hv : ∀ i, ∃ j, j ≠ 0 ∧ j ≠ Fin.last (n + 1) ∧ s i = p j) :
    p 0 ∈ polygonExterior s ∧ p (Fin.last (n + 1)) ∈ polygonExterior s := by
  classical
  let Xc : E →L[ℝ] ℝ := X.toContinuousLinearMap
  let y := p (Fin.last (n + 1)) - p 0
  have hy : Xc y ≠ 0 := by
    change X (p (Fin.last (n + 1)) - p 0) ≠ 0
    rw [map_sub]
    exact ne_of_gt (sub_pos.mpr hLR)
  have hsurj : Function.Surjective Xc := by
    intro t
    refine ⟨(t / Xc y) • y, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hy]
  have hneg : Function.Surjective (-Xc) := by
    intro t
    obtain ⟨x, hx⟩ := hsurj (-t)
    refine ⟨x, ?_⟩
    change -(Xc x) = t
    rw [hx, neg_neg]
  have hbound (L : E →L[ℝ] ℝ) (hL : Function.Surjective L) (x : E)
      (hx : ∀ i, L x < L (s i)) : x ∈ polygonExterior s := by
    have huniv : (Finset.univ : Finset (Fin d)).Nonempty :=
      ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ
      (fun i => L (s i)) huniv
    exact polygonExterior_of_lt_vertex_bound s L hL (L (s j))
      (fun i => hj i (Finset.mem_univ i)) (hx j)
  constructor
  · apply hbound Xc hsurj
    intro i
    obtain ⟨j, hj0, hjl, hj⟩ := hv i
    rw [hj]
    exact (hX j hj0 hjl).1
  · apply hbound (-Xc) hneg
    intro i
    obtain ⟨j, hj0, hjl, hj⟩ := hv i
    rw [hj]
    exact neg_lt_neg (hX j hj0 hjl).2

omit [FiniteDimensional ℝ E] in
private theorem consecutive_subarc_internal_vertices {n ell : ℕ}
    (p : Polygon E (n + 2)) (a b : Fin (n + 2))
    (ha0 : a ≠ 0) (hal : a ≠ Fin.last (n + 1))
    (hb0 : b ≠ 0) (hbl : b ≠ Fin.last (n + 1))
    (hlen : ell + 1 = Nat.dist a.val b.val) (q : Polygon E (ell + 2))
    (hvertices : ∀ j : Fin (ell + 2), q j = polygonLinearParameter p
      (if a < b then (a.val : ℝ) + j.val else (a.val : ℝ) - j.val)) :
    ∀ j, ∃ i, i ≠ 0 ∧ i ≠ Fin.last (n + 1) ∧ q j = p i := by
  have hinc (h : a < b) : a.val + (ell + 1) = b.val := by
    rw [Nat.dist_eq_sub_of_le (show a.val ≤ b.val from h.le)] at hlen
    omega
  have hdec (h : ¬ a < b) : b.val + (ell + 1) = a.val := by
    rw [Nat.dist_eq_sub_of_le_right (show b.val ≤ a.val from le_of_not_gt h)] at hlen
    omega
  let f : Fin (ell + 2) → Fin (n + 2) := fun j =>
    ⟨if a < b then a.val + j.val else a.val - j.val, by
      split_ifs with h
      · have := hinc h
        omega
      · have := hdec h
        omega⟩
  have hqf (j : Fin (ell + 2)) : q j = p (f j) := by
    rw [hvertices j, ← polygonLinearParameter_natVertex p (f j)]
    congr 1
    by_cases h : a < b
    · simp only [f, if_pos h, Nat.cast_add]
    · have hj : j.val ≤ a.val := by have := hdec h; omega
      simp only [f, if_neg h, Nat.cast_sub hj]
  have hapos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
  have hbpos : 0 < b.val := Nat.pos_of_ne_zero (fun h => hb0 (Fin.ext h))
  have halt : a.val < n + 1 := Fin.lt_last_iff_ne_last.mpr hal
  have hblt : b.val < n + 1 := Fin.lt_last_iff_ne_last.mpr hbl
  intro j
  have hbounds : 0 < (f j).val ∧ (f j).val < n + 1 := by
    by_cases h : a < b
    · have := hinc h
      simp only [f, if_pos h]
      constructor <;> omega
    · have := hdec h
      simp only [f, if_neg h]
      constructor <;> omega
  refine ⟨f j, ?_, ?_, hqf j⟩
  · intro hz
    have := congrArg Fin.val hz
    simp only [Fin.val_zero] at this
    omega
  · intro hl
    have := congrArg Fin.val hl
    simp only [Fin.val_last] at this
    omega

omit [FiniteDimensional ℝ E] in
private theorem terminal_local_crossings {n k : ℕ}
    (_hdim : Module.finrank ℝ E = 2)
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (hk : 2 ≤ k) (u : Fin (n + 2))
    (cT : Fin (k + 1) ↪ Fin (n + 2))
    (_hcT0 : cT 0 = u)
    (hcTint : ∀ i, cT i ≠ 0 ∧ cT i ≠ Fin.last (n + 1))
    (hadj : cT (Fin.last k) = (finRotate (n + 2)).symm (cT 0) ∨
      cT (Fin.last k) = finRotate (n + 2) (cT 0))
    (hwnot : (if cT (Fin.last k) = (finRotate (n + 2)).symm (cT 0)
      then finRotate (n + 2) (cT 0) else (finRotate (n + 2)).symm (cT 0)) ∉ range cT)
    (g : Fin (n + 2) → Fin (n + 2))
    (hcTnext : ∀ i : Fin k, cT i.succ = g (cT i.castSucc))
    (hcTA : ∀ i : Fin k,
      cT i.castSucc ≠ 0 ∧ cT i.castSucc ≠ Fin.last (n + 1) ∧
        ¬ IsAdmissibleArcVertex p (cT i.castSucc))
    (hcand : ∀ x : Fin (n + 2),
      x ≠ 0 → x ≠ Fin.last (n + 1) → ¬ IsAdmissibleArcVertex p x →
      ∃ f : E ≃ᴬ[ℝ] (ℝ × ℝ),
        f (p x) = (0, 0) ∧
        f (p ((finRotate (n + 2)).symm x)) = (1, 0) ∧
        f (p (finRotate (n + 2) x)) = (0, 1) ∧
        g x ≠ 0 ∧ g x ≠ Fin.last (n + 1) ∧ g x ≠ x ∧
        g x ≠ (finRotate (n + 2)).symm x ∧ g x ≠ finRotate (n + 2) x ∧
        f (p (g x)) ∈ unitTriangle ∧
        0 < (f (p (g x))).1 ∧ 0 < (f (p (g x))).2 ∧
        (∀ l, l ≠ x → l ≠ (finRotate (n + 2)).symm x →
          l ≠ finRotate (n + 2) x → f (p l) ∈ unitTriangle →
          (f (p (g x))).1 + (f (p (g x))).2 ≤
            (f (p l)).1 + (f (p l)).2) ∧
        Disjoint (openSegment ℝ (p x) (p (g x))) (polygonArcBoundary p))
    (hvis : ∀ j : Fin k,
      Disjoint (openSegment ℝ (p (cT j.castSucc)) (p (cT j.succ)))
        (polygonArcBoundary p))
    (hinc : ∀ i j : Fin k, i ≠ j →
      segment ℝ (p (cT i.castSucc)) (p (cT i.succ)) ∩
          segment ℝ (p (cT j.castSucc)) (p (cT j.succ)) =
        {p (cT i.castSucc), p (cT i.succ)} ∩
          {p (cT j.castSucc), p (cT j.succ)}) :
    ∀ i : Fin (k + 1), i ≠ 0 → i ≠ Fin.last k →
      ∃ ε : ℝ, 0 < ε ∧ ∃ W A B : Set E,
        IsOpen W ∧ p (cT i) ∈ W ∧
        IsPreconnected A ∧ IsPreconnected B ∧
        A ∪ B = W \ (Polygon.mk (fun j => p (cT j))).boundary ℝ ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (p (cT i))
          (p ((finRotate (n + 2)).symm (cT i))) t ∈ A) ∧
        (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (p (cT i))
          (p (finRotate (n + 2) (cT i))) t ∈ B) := by
  classical
  obtain ⟨hr, hedge, _, _, _, _⟩ :=
    hp.terminal_path_isSimplePolygon hk cT hcTint hadj hwnot hvis hinc
  let r : Polygon E (k + 1) := ⟨fun j => p (cT j)⟩
  have hri (j : Fin (k + 1)) : r j = p (cT j) := rfl
  intro i hi0 hilast
  have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi0 (Fin.ext h))
  have hi_lt : i.val < k := Fin.lt_last_iff_ne_last.mpr hilast
  let a0 : Fin k := ⟨i.val - 1, by omega⟩
  let b0 : Fin k := ⟨i.val, hi_lt⟩
  have hb_cast : b0.castSucc = i := by
    apply Fin.ext
    rfl
  have ha_succ : a0.succ = i := by
    apply Fin.ext
    dsimp [a0]
    omega
  have hb_succ : b0.succ = ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext
    rfl
  let ipV : Fin (k + 1) := a0.castSucc
  let inext : Fin (k + 1) := b0.succ
  let ipEdge : Fin (k + 1) := (finRotate (k + 1)).symm i
  have hipEdge : ipEdge = ipV := by
    apply (finRotate (k + 1)).injective
    rw [Equiv.apply_symm_apply]
    calc
      i = a0.succ := ha_succ.symm
      _ = finRotate (k + 1) a0.castSucc := by
        symm
        apply finRotate_of_lt
        exact a0.isLt
  have hgl : g (cT ipV) = cT i := by
    have hh := hcTnext a0
    rw [ha_succ] at hh
    exact hh.symm
  have hgk : g (cT i) = cT inext := by
    have hh := hcTnext b0
    rw [hb_cast, hb_succ] at hh
    exact hh.symm
  have hlB := hcTA a0
  have hkB := hcTA b0
  have hl0 : cT ipV ≠ 0 := by simpa [ipV] using hlB.1
  have hll : cT ipV ≠ Fin.last (n + 1) := by simpa [ipV] using hlB.2.1
  have hkl0 : cT i ≠ 0 := by simpa [hb_cast] using hkB.1
  have hkll : cT i ≠ Fin.last (n + 1) := by simpa [hb_cast] using hkB.2.1
  have hla := hcand (cT ipV) hl0 hll hlB.2.2
  rw [hgl] at hla
  obtain ⟨F, hFl, hFp, hFs, h0, hlast, hne, hpred, hsucc, hT,
    hpos1, hpos2, hmin, _⟩ := hla
  have hheight := hp.normalized_minimal_candidate_neighbor_height (cT ipV) (cT i) F
    hl0 hll h0 hlast hFl hFp hFs hne hpred hsucc hT hmin
  let H : E →ᵃ[ℝ] ℝ :=
    (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).toAffineMap.comp
      F.toAffineEquiv.toAffineMap
  have hHl : H (p (cT ipV)) < H (p (cT i)) := by
    change (F (p (cT ipV))).1 + (F (p (cT ipV))).2 <
      (F (p (cT i))).1 + (F (p (cT i))).2
    rw [hFl]
    simpa only [Prod.fst, Prod.snd, zero_add] using add_pos hpos1 hpos2
  have hka := hcand (cT i) hkl0 hkll hkB.2.2
  rw [hgk] at hka
  obtain ⟨f, hfk, hfp, hfs, _, _, _, _, _, _, hjpos1, hjpos2, _⟩ := hka
  obtain ⟨U, hU, hiU, hUeq⟩ := exists_open_iUnion_eq_of_mem_imp
    (fun a : Fin (k + 1) => r.edgeSet ℝ a)
    (fun a => (polygon_edgeSet_isCompact r a).isClosed) {ipEdge, i} (r i) (by
      intro a ha
      rcases (hr.vertex_mem_edgeSet_iff i a).mp ha with hh | hh
      · exact Or.inr hh.symm
      · left
        apply (finRotate (k + 1)).injective
        exact hh.symm.trans ((finRotate (k + 1)).apply_symm_apply i).symm)
  have hipedge : r.edgeSet ℝ ipEdge = segment ℝ (p (cT i)) (p (cT ipV)) := by
    calc
      r.edgeSet ℝ ipEdge = r.edgeSet ℝ ipV := by rw [hipEdge]
      _ = r.edgeSet ℝ a0.castSucc := by rfl
      _ = segment ℝ (p (cT a0.castSucc)) (p (cT a0.succ)) := hedge a0
      _ = segment ℝ (p (cT i)) (p (cT ipV)) := by
        rw [ha_succ, segment_symm]
  have hiedge : r.edgeSet ℝ i = segment ℝ (p (cT i)) (p (cT inext)) := by
    rw [← hb_cast, hedge b0]
  have hClocal (x : E) (hx : x ∈ U) :
      x ∈ r.boundary ℝ ↔
        x ∈ segment ℝ (p (cT i)) (p (cT ipV)) ∪
          segment ℝ (p (cT i)) (p (cT inext)) := by
    have hh := hUeq x hx
    change x ∈ r.boundary ℝ ↔ _ at hh
    rw [hh]
    constructor
    · rintro ⟨a, ha, hxa⟩
      rcases ha with rfl | rfl
      · exact Or.inl (hipedge ▸ hxa)
      · exact Or.inr (hiedge ▸ hxa)
    · rintro (hx' | hx')
      · exact ⟨ipEdge, Or.inl rfl, hipedge.symm ▸ hx'⟩
      · exact ⟨i, Or.inr rfl, hiedge.symm ▸ hx'⟩
  obtain ⟨e, rho, eps, _, _, _, _, _, _, _, heps, _, hW, hkW, _, _,
      hCm, hCp, _, hcover, _, _, _, _, _, _, _, _, _, hrays⟩ :=
    exists_local_alternating_sides_at_arc_vertex hp (cT i) (cT ipV) (cT inext)
      hkl0 hkll f H hfk hfp hfs ⟨hjpos1, hjpos2⟩ hHl hheight.1 hheight.2
      (r.boundary ℝ) U univ hU (hri i ▸ hiU) hClocal isOpen_univ (mem_univ _)
  refine ⟨eps, heps, e ⁻¹' (Ioo (-rho) rho ×ˢ Ioo (-rho) rho),
    e ⁻¹' (Ioo (-rho) rho ×ˢ Ioo 0 rho),
    e ⁻¹' (Ioo (-rho) rho ×ˢ Ioo (-rho) 0), hW,
    (hri i).symm ▸ hkW, hCp.isPreconnected, hCm.isPreconnected, ?_, ?_, ?_⟩
  · rw [union_comm]
    exact hcover
  · intro t ht
    rw [hri]
    exact (hrays t ht).1
  · intro t ht
    rw [hri]
    exact (hrays t ht).2.1




theorem IsSimplePolygonalArc.exists_admissible_away_neighbors
    {n : ℕ} {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (hdim : Module.finrank ℝ E = 2) (X : E →ₗ[ℝ] ℝ)
    (hLR : X (p 0) < X (p (Fin.last (n + 1))))
    (hX : ∀ i, i ≠ 0 → i ≠ Fin.last (n + 1) →
      X (p 0) < X (p i) ∧ X (p i) < X (p (Fin.last (n + 1))))
    (u : Fin (n + 2)) (hu0 : u ≠ 0) (hul : u ≠ Fin.last (n + 1))
    (huad : ¬ IsAdmissibleArcVertex p u) :
    ∃ i, IsAdmissibleArcVertex p i ∧
      i ≠ (finRotate (n + 2)).symm u ∧ i ≠ finRotate (n + 2) u := by
  classical
  obtain ⟨ei, ej, hei, hej, hep, hes, _⟩ :=
    exists_arc_incident_edge_indices u hu0 hul
  have hup : u ≠ (finRotate (n + 2)).symm u := by
    rw [← hep, ← hei]
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hus : u ≠ finRotate (n + 2) u := by
    rw [← hes, ← hej]
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hps : (finRotate (n + 2)).symm u ≠ finRotate (n + 2) u := by
    intro hh
    have hv := congrArg Fin.val (hep.trans (hh.trans hes.symm))
    have hu := congrArg Fin.val (hei.trans hej.symm)
    simp only [Fin.val_succ, Fin.val_castSucc] at hv hu
    omega
  by_cases had : IsAdmissibleArcVertex p u
  · exact ⟨u, had, hup, hus⟩
  obtain ⟨g, N, hout, hcand, h1, h2, hvis, hinc, hN, hact, hinj,
      hthrough, hevent⟩ :=
    hp.exists_minimal_candidate_orbit hdim X hLR hX u hu0 hul huad
  let v (t : ℕ) := g^[t] u
  rcases hevent with ⟨hexit, hinjExit⟩ | hC
  · exact ⟨v N, hexit, hinjExit.1, hinjExit.2.1⟩
  rcases hC with
    ⟨hterm, htwo, hinjT, cT, hcT, hcT0, hcTlast, hcnextT, hcinternal,
      hcA, hcw⟩ | ⟨j, hclose⟩
  · let r : Polygon E (N + 1) := ⟨fun i => p (cT i)⟩
    have hcA_B (i : Fin N) : cT i.castSucc ∈
        {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
          ¬ IsAdmissibleArcVertex p k} := by
      simpa only [Set.mem_ofPred_eq] using (hcA i).1
    have hvisT (i : Fin N) :
        Disjoint (openSegment ℝ (p (cT i.castSucc)) (p (cT i.succ)))
          (polygonArcBoundary p) := by
      simpa only [hcnextT i] using hvis (cT i.castSucc) (hcA i).1
    have hincT (i j : Fin N) (hij : i ≠ j) :
        segment ℝ (p (cT i.castSucc)) (p (cT i.succ)) ∩
            segment ℝ (p (cT j.castSucc)) (p (cT j.succ)) =
          {p (cT i.castSucc), p (cT i.succ)} ∩
            {p (cT j.castSucc), p (cT j.succ)} := by
      have hne : cT i.castSucc ≠ cT j.castSucc := by
        intro hh
        have heq := cT.injective hh
        apply hij
        apply Fin.ext
        simpa only [Fin.val_castSucc] using congrArg Fin.val heq
      simpa only [hcnextT i, hcnextT j] using
        hinc (cT i.castSucc) (hcA i).1 (cT j.castSucc) (hcA j).1 hne
    have hterm' : cT (Fin.last N) = (finRotate (n + 2)).symm (cT 0) ∨
        cT (Fin.last N) = finRotate (n + 2) (cT 0) := by
      rw [hcTlast, hcT0]
      exact hterm
    have hcw' : (if cT (Fin.last N) = (finRotate (n + 2)).symm (cT 0)
        then finRotate (n + 2) (cT 0) else (finRotate (n + 2)).symm (cT 0)) ∉
        range cT := by
      simpa only [hcTlast, hcT0] using hcw
    obtain ⟨hr, hedgeT, hlastT, hboundaryT, hcontactT, hfree⟩ :=
      hp.terminal_path_isSimplePolygon htwo cT hcinternal hterm' hcw' hvisT hincT
    have hend := exterior_endpoints_of_internal_vertices p X hLR hX r (by omega)
      (fun i => ⟨cT i, (hcinternal i).1, (hcinternal i).2, rfl⟩)
    have hcrossT := terminal_local_crossings hdim hp htwo u cT hcT0 hcinternal
      hterm' hcw' g hcnextT
      (fun i => by
        exact ⟨(hcA_B i).1, (hcA_B i).2.1, (hcA_B i).2.2⟩)
      (fun x hx0 hxl had => hcand x ⟨hx0, hxl, had⟩)
      hvisT hincT
    have huB : u ∈ {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
        ¬ IsAdmissibleArcVertex p k} := ⟨hu0, hul, huad⟩
    obtain ⟨f, hf0, hfp, hfs, _, _, _, _, _, _, hfpos1, hfpos2, _⟩ :=
      hcand u huB
    have hcOne : cT ⟨1, by omega⟩ = g u := by
      have hh := hcnextT (⟨0, by omega⟩ : Fin N)
      have hsucc0 : (⟨0, by omega⟩ : Fin N).succ = ⟨1, by omega⟩ := by
        apply Fin.ext
        rfl
      have hcast0 : (⟨0, by omega⟩ : Fin N).castSucc = (0 : Fin (N + 1)) := by
        apply Fin.ext
        rfl
      rw [hsucc0, hcast0, hcT0] at hh
      exact hh
    have hf0' : f (p (cT 0)) = (0, 0) := by
      rw [hcT0]
      exact hf0
    have hfp' : f (p ((finRotate (n + 2)).symm (cT 0))) = (1, 0) := by
      rw [hcT0]
      exact hfp
    have hfs' : f (p (finRotate (n + 2) (cT 0))) = (0, 1) := by
      rw [hcT0]
      exact hfs
    have hfpos : 0 < (f (p (cT ⟨1, by omega⟩))).1 ∧
        0 < (f (p (cT ⟨1, by omega⟩))).2 := by
      rw [hcOne]
      exact ⟨hfpos1, hfpos2⟩
    obtain ⟨j, hjpos, hS, hmeet, hw, hv, hvisj, ell, q, hlen, hsimple,
      hq0, hq1, hqv, hqparam, hqboundary, hqopen⟩ :=
      hp.exists_terminal_path_good_subarc hdim htwo cT hcinternal hterm' hcw'
        f hf0' hfp' hfs' hfpos hr hcontactT hend.1 hend.2 hcrossT hvisT
    have hja : cT j.castSucc ≠ 0 ∧ cT j.castSucc ≠ Fin.last (n + 1) ∧
        ¬ IsAdmissibleArcVertex p (cT j.castSucc) := by
      simpa only [Set.mem_ofPred_eq] using (hcA j).1
    have hjb : cT j.succ ≠ 0 ∧ cT j.succ ≠ Fin.last (n + 1) :=
      hcinternal j.succ
    have hab : cT j.castSucc ≠ cT j.succ := by
      intro hh
      have hd := hlen
      rw [hh] at hd
      simp at hd
    obtain ⟨aidx, hlow, hupp, hadm, _⟩ :=
      hp.exists_admissible_between_of_visible_subarc hdim
        (cT j.castSucc) (cT j.succ) hab hja.1 hja.2.1 hjb.1 hjb.2
        hlen q hqv hvisj
        (by
          obtain ⟨h0, _⟩ := exterior_endpoints_of_internal_vertices p X hLR hX q
            (by omega)
            (consecutive_subarc_internal_vertices p (cT j.castSucc) (cT j.succ)
              hja.1 hja.2.1 hjb.1 hjb.2 hlen q hqv)
          exact h0)
        (by
          obtain ⟨_, hl⟩ := exterior_endpoints_of_internal_vertices p X hLR hX q
            (by omega)
            (consecutive_subarc_internal_vertices p (cT j.castSucc) (cT j.succ)
              hja.1 hja.2.1 hjb.1 hjb.2 hlen q hqv)
          exact hl)
    have hmemT : p aidx ∈ polygonLinearParameter p '' Icc
        (min ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ))
        (max ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ)) := by
      exact ⟨(aidx.val : ℝ), ⟨by exact_mod_cast hlow.le,
        by exact_mod_cast hupp.le⟩,
        polygonLinearParameter_natVertex p aidx⟩
    have hmemS : p aidx ∈ polygonLinearParameter p '' Ioo
        (min ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ))
        (max ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ)) := by
      exact ⟨(aidx.val : ℝ), ⟨by exact_mod_cast hlow,
        by exact_mod_cast hupp⟩,
        polygonLinearParameter_natVertex p aidx⟩
    have haway : aidx ≠ (finRotate (n + 2)).symm u ∧
        aidx ≠ finRotate (n + 2) u := by
      rcases hterm' with hvpred | hvsucc
      · have hw' : p (finRotate (n + 2) u) ∉
            polygonLinearParameter p '' Icc
              (min ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ))
              (max ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ)) := by
          simpa [hvpred, hcT0] using hw
        have hv' : p ((finRotate (n + 2)).symm u) ∉
            polygonLinearParameter p '' Ioo
              (min ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ))
              (max ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ)) := by
          simpa [hvpred, hcT0] using hv
        exact ⟨fun hh => hv' (hh ▸ hmemS), fun hh => hw' (hh ▸ hmemT)⟩
      · have hw' : p ((finRotate (n + 2)).symm u) ∉
            polygonLinearParameter p '' Icc
              (min ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ))
              (max ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ)) := by
          have hsp : finRotate (n + 2) u ≠ (finRotate (n + 2)).symm u := by
            intro hh
            exact hps hh.symm
          simpa only [hvsucc, hcT0, if_neg hsp] using hw
        have hv' : p (finRotate (n + 2) u) ∉
            polygonLinearParameter p '' Ioo
              (min ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ))
              (max ((cT j.castSucc).val : ℝ) ((cT j.succ).val : ℝ)) := by
          have hsp : finRotate (n + 2) u ≠ (finRotate (n + 2)).symm u := by
            intro hh
            exact hps hh.symm
          simpa only [hvsucc, hcT0, if_neg hsp] using hv
        exact ⟨fun hh => hw' (hh ▸ hmemT), fun hh => hv' (hh ▸ hmemS)⟩
    exact ⟨aidx, hadm, haway.1, haway.2⟩
  · rcases hclose with
      ⟨hEq, hthree, c, r, hc, hrv, hr, hnext, hedge, hcontact,
        hleft, hright, hcross⟩
    let m := N - j.val
    have hbound (i : Fin m) : j.val + i.val < N := by
      have hi := i.isLt
      dsimp [m] at hi ⊢
      omega
    have hri (i : Fin m) : r i = p (c i) := by
      rw [hrv]
    have hcA (i : Fin m) : c i ∈
        {k : Fin (n + 2) | k ∈
          {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
            ¬ IsAdmissibleArcVertex p k} ∧
          k ≠ (finRotate (n + 2)).symm u ∧ k ≠ finRotate (n + 2) u} := hnext i |>.1
    have hcnext (i : Fin m) : c (finRotate m i) = g (c i) := by
      have hh := (hnext i).2
      exact hh
    obtain ⟨i, k, q, hai, hlen, hsimple, hq0, hq1, hqv, hqparam,
      hqboundary, hqopen, hS, hmeet, hwu, hwp, hvisq⟩ :=
      exists_cycle_good_subarc hp hr hdim c (fun i => hri i)
        (fun i => by
          have hi : c i ≠ 0 ∧ c i ≠ Fin.last (n + 1) ∧
              ¬ IsAdmissibleArcVertex p (c i) := by
            simpa only [Set.mem_ofPred_eq] using (hcA i).1
          exact ⟨hi.1, hi.2.1⟩) hcontact
        hleft hright
        u hu0 hul
        (fun i => ⟨(hcA i).2.1, (hcA i).2.2⟩)
        (fun i => by
          rw [hcnext]
          exact hvis (c i) (hcA i).1)
        (fun i => by
          obtain ⟨eps, heps, W, A, B, hW, hriW, hAp, hBp, hcover,
            hpred, hsucc⟩ := hcross i
          exact ⟨eps, heps, W, A, B, hW, hriW, hAp, hBp,
            hcover, hpred, hsucc⟩)
    obtain ⟨aidx, hlow, hupp, hadm, _⟩ :=
      hp.exists_admissible_between_of_visible_subarc hdim
        (c i) (c (finRotate m i)) (by
          intro hh
          exact hai (by simpa only [m] using hh))
        (hcA i).1.1 (hcA i).1.2.1
        (hcA (finRotate m i)).1.1 (hcA (finRotate m i)).1.2.1
        hlen q hqv hvisq
        (by
          obtain ⟨h0, _⟩ := exterior_endpoints_of_internal_vertices p X hLR hX q
            (by omega)
            (consecutive_subarc_internal_vertices p (c i) (c (finRotate m i))
              (hcA i).1.1 (hcA i).1.2.1 (hcA (finRotate m i)).1.1
              (hcA (finRotate m i)).1.2.1 hlen q hqv)
          exact h0)
        (by
          obtain ⟨_, hl⟩ := exterior_endpoints_of_internal_vertices p X hLR hX q
            (by omega)
            (consecutive_subarc_internal_vertices p (c i) (c (finRotate m i))
              (hcA i).1.1 (hcA i).1.2.1 (hcA (finRotate m i)).1.1
              (hcA (finRotate m i)).1.2.1 hlen q hqv)
          exact hl)
    have haway : aidx ≠ (finRotate (n + 2)).symm u ∧
        aidx ≠ finRotate (n + 2) u := by
      have hmem : p aidx ∈ polygonLinearParameter p '' Icc
          (min ((c i).val : ℝ) ((c (finRotate m i)).val : ℝ))
          (max ((c i).val : ℝ) ((c (finRotate m i)).val : ℝ)) := by
        exact ⟨(aidx.val : ℝ), ⟨by exact_mod_cast hlow.le,
          by exact_mod_cast hupp.le⟩,
          polygonLinearParameter_natVertex p aidx⟩
      exact ⟨fun hh => hwu (hh ▸ hmem), fun hh => hwp (hh ▸ hmem)⟩
    exact ⟨aidx, hadm, haway.1, haway.2⟩

end PoincareConjecture.M25.Topology3D
