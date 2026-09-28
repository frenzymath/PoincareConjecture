import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcCandidateMap
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcAuxiliaryCycle
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcAlternatingSides
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.RegionBounds
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsSimplePolygonalArc.exists_minimal_candidate_orbit
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    {n : ℕ} {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (X : E →ₗ[ℝ] ℝ) (hLR : X (p 0) < X (p (Fin.last (n + 1))))
    (hX : ∀ i, i ≠ 0 → i ≠ Fin.last (n + 1) →
      X (p 0) < X (p i) ∧ X (p i) < X (p (Fin.last (n + 1))))
    (u : Fin (n + 2)) (hu0 : u ≠ 0) (hul : u ≠ Fin.last (n + 1))
    (huad : ¬ IsAdmissibleArcVertex p u) :
    let B := {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
      ¬ IsAdmissibleArcVertex p k}
    ∃ g : Fin (n + 2) → Fin (n + 2), ∃ N : ℕ,
      (∀ k, k ∉ B → g k = k) ∧
      (∀ k ∈ B, ∃ f : E ≃ᴬ[ℝ] (ℝ × ℝ),
        f (p k) = (0, 0) ∧ f (p ((finRotate (n + 2)).symm k)) = (1, 0) ∧
        f (p (finRotate (n + 2) k)) = (0, 1) ∧
        g k ≠ 0 ∧ g k ≠ Fin.last (n + 1) ∧ g k ≠ k ∧
        g k ≠ (finRotate (n + 2)).symm k ∧ g k ≠ finRotate (n + 2) k ∧
        f (p (g k)) ∈ unitTriangle ∧ 0 < (f (p (g k))).1 ∧
        0 < (f (p (g k))).2 ∧
        (∀ l, l ≠ k → l ≠ (finRotate (n + 2)).symm k →
          l ≠ finRotate (n + 2) k → f (p l) ∈ unitTriangle →
          (f (p (g k))).1 + (f (p (g k))).2 ≤ (f (p l)).1 + (f (p l)).2) ∧
        Disjoint (openSegment ℝ (p k) (p (g k))) (polygonArcBoundary p)) ∧
      (∀ k ∈ B, g k ≠ k) ∧
      (∀ k ∈ B, g k ∈ B → g (g k) ≠ k) ∧
      (∀ k ∈ B, Disjoint (openSegment ℝ (p k) (p (g k))) (polygonArcBoundary p)) ∧
      (∀ k ∈ B, ∀ l ∈ B, k ≠ l →
        segment ℝ (p k) (p (g k)) ∩ segment ℝ (p l) (p (g l)) =
          {p k, p (g k)} ∩ {p l, p (g l)}) ∧
      let A := {k : Fin (n + 2) | k ∈ B ∧
        k ≠ (finRotate (n + 2)).symm u ∧ k ≠ finRotate (n + 2) u}
      let v := fun t : ℕ => g^[t] u
      0 < N ∧ (∀ t : ℕ, t < N → v t ∈ A) ∧
      Function.Injective (fun i : Fin N => v i.val) ∧
      (∀ t : ℕ, t ≤ N → v t ≠ 0 ∧ v t ≠ Fin.last (n + 1)) ∧
      ((IsAdmissibleArcVertex p (v N) ∧ v N ≠ (finRotate (n + 2)).symm u ∧
          v N ≠ finRotate (n + 2) u ∧
          Function.Injective (fun i : Fin (N + 1) => v i.val)) ∨
        ((v N = (finRotate (n + 2)).symm u ∨ v N = finRotate (n + 2) u) ∧
          2 ≤ N ∧ Function.Injective (fun i : Fin (N + 1) => v i.val) ∧
          ∃ cT : Fin (N + 1) ↪ Fin (n + 2),
            (∀ i, cT i = v i.val) ∧ cT 0 = u ∧ cT (Fin.last N) = v N ∧
            (∀ i : Fin N, cT i.succ = g (cT i.castSucc)) ∧
            (∀ i, cT i ≠ 0 ∧ cT i ≠ Fin.last (n + 1)) ∧
            (∀ i : Fin N, cT i.castSucc ∈ A) ∧
            (let w := if v N = (finRotate (n + 2)).symm u
              then finRotate (n + 2) u else (finRotate (n + 2)).symm u
             w ∉ range cT)) ∨
        ∃ j : Fin N, v N = v j.val ∧
          let m := N - j.val
          3 ≤ m ∧ ∃ c : Fin m ↪ Fin (n + 2), ∃ r : Polygon E m,
            (∀ i, c i = v (j.val + i.val)) ∧ r = Polygon.mk (fun i => p (c i)) ∧
            IsSimplePolygon r ∧
            (∀ i, c i ∈ A ∧ c (finRotate m i) = g (c i)) ∧
            (∀ i, r.edgeSet ℝ i = segment ℝ (p (c i)) (p (g (c i)))) ∧
            r.boundary ℝ ∩ polygonArcBoundary p = range r ∧
            p 0 ∈ polygonExterior r ∧ p (Fin.last (n + 1)) ∈ polygonExterior r ∧
            (∀ i, ∃ eps : ℝ, 0 < eps ∧ ∃ W Sm Sp : Set E,
              IsOpen W ∧ r i ∈ W ∧ IsPreconnected Sm ∧ IsPreconnected Sp ∧
              Sm ∪ Sp = W \ r.boundary ℝ ∧
              (∀ t ∈ Ioo 0 eps,
                AffineMap.lineMap (r i) (p ((finRotate (n + 2)).symm (c i))) t ∈ Sm) ∧
              (∀ t ∈ Ioo 0 eps,
                AffineMap.lineMap (r i) (p (finRotate (n + 2) (c i))) t ∈ Sp))) := by
  classical
  dsimp only
  let B := {k : Fin (n + 2) | k ≠ 0 ∧ k ≠ Fin.last (n + 1) ∧
    ¬ IsAdmissibleArcVertex p k}
  obtain ⟨g, hout, hcand, h1, h2, hvis, hinc⟩ :=
    hp.exists_minimal_arc_candidate_map hdim X hLR hX
  let A := {k : Fin (n + 2) | k ∈ B ∧
    k ≠ (finRotate (n + 2)).symm u ∧ k ≠ finRotate (n + 2) u}
  let v (t : ℕ) := g^[t] u
  have hstep (t : ℕ) : v (t + 1) = g (v t) := Function.iterate_succ_apply' g t u
  obtain ⟨ei, ej, hei, hej, hep, hes, _⟩ := exists_arc_incident_edge_indices u hu0 hul
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
  have huB : u ∈ B := ⟨hu0, hul, huad⟩
  obtain ⟨N, hN, hact, hinj, hevent⟩ :=
    exists_first_orbit_exit_or_repeat g A u ⟨huB, hup, hus⟩
  have hthrough (t : ℕ) (ht : t ≤ N) : v t ≠ 0 ∧ v t ≠ Fin.last (n + 1) := by
    by_cases hlt : t < N
    · exact ⟨(hact t hlt).1.1, (hact t hlt).1.2.1⟩
    · have htN : t = N := by omega
      subst t
      have hprev := (hact (N - 1) (by omega)).1
      obtain ⟨_, _, _, _, hzero, hlast, _⟩ := hcand (v (N - 1)) hprev
      rw [show N = (N - 1) + 1 from by omega, hstep]
      exact ⟨hzero, hlast⟩
  refine ⟨g, N, hout, hcand, h1, h2, hvis, hinc, hN, hact, hinj, hthrough, ?_⟩
  rcases hevent with ⟨hexit, hinjT⟩ | ⟨j, hclose⟩
  · by_cases hn : v N = (finRotate (n + 2)).symm u ∨ v N = finRotate (n + 2) u
    · right; left
      have htwo : 2 ≤ N := by
        by_contra hh
        have hNeq : N = 1 := by omega
        obtain ⟨_, _, _, _, _, _, _, hgp, hgs, _⟩ := hcand u huB
        have hv1 : v N = g u := by simp [v, hNeq]
        exact hn.elim (fun h => hgp (hv1.symm.trans h)) (fun h => hgs (hv1.symm.trans h))
      let cT : Fin (N + 1) ↪ Fin (n + 2) := ⟨fun i => v i.val, hinjT⟩
      refine ⟨hn, htwo, hinjT, cT, fun _ => rfl, rfl, rfl,
        fun i => hstep i.val, fun i => hthrough i.val (by omega),
        fun i => hact i.val i.isLt, ?_⟩
      rintro ⟨i, hi⟩
      change v i.val = _ at hi
      by_cases hiN : i.val < N
      · have hai := hact i.val hiN
        split_ifs at hi with hh
        · exact hai.2.2 hi
        · exact hai.2.1 hi
      · have hiN' : i.val = N := by omega
        rw [hiN'] at hi
        split_ifs at hi with hh
        · exact hps (hh.symm.trans hi)
        · exact hh hi
    · left
      have hnp : v N ≠ (finRotate (n + 2)).symm u := fun h => hn (Or.inl h)
      have hns : v N ≠ finRotate (n + 2) u := fun h => hn (Or.inr h)
      refine ⟨?_, hnp, hns, hinjT⟩
      by_contra had
      exact hexit ⟨⟨(hthrough N le_rfl).1, (hthrough N le_rfl).2, had⟩, hnp, hns⟩
  · right; right
    obtain ⟨hthree, r, hrv, hr, hnext, hedge, hcontact⟩ :=
      exists_simplePolygon_of_first_orbit_repeat g A u p (polygonArcBoundary p)
        hp.vertices_injective (polygon_vertex_mem_arcBoundary p)
        (fun k hk => h1 k hk.1) (fun k hk hk' => h2 k hk.1 hk'.1)
        (fun k hk => hvis k hk.1) (fun k hk l hl hkl => hinc k hk.1 l hl.1 hkl)
        N j.val j.isLt hact hinj hclose
    let m := N - j.val
    have hbound (i : Fin m) : j.val + i.val < N := by have := i.isLt; dsimp [m] at *; omega
    let c : Fin m ↪ Fin (n + 2) := ⟨fun i => v (j.val + i.val), by
      intro i k hh
      have hv := congrArg Fin.val
        (hinj (a₁ := ⟨j.val + i.val, hbound i⟩) (a₂ := ⟨j.val + k.val, hbound k⟩) hh)
      apply Fin.ext
      dsimp only at hv
      omega⟩
    have hri (i : Fin m) : r i = p (c i) := hrv i
    have hre : r = Polygon.mk (fun i => p (c i)) := by
      cases r
      congr 1
      exact funext hri
    have hcA (i : Fin m) : c i ∈ A := (hnext i).1
    have hcnext (i : Fin m) : c (finRotate m i) = g (c i) := (hnext i).2
    let Xc : E →L[ℝ] ℝ := X.toContinuousLinearMap
    let y := p (Fin.last (n + 1)) - p 0
    have hdy : 0 < X y := by dsimp [y]; rw [map_sub]; exact sub_pos.mpr hLR
    have hsurj : Function.Surjective Xc := by
      intro t
      refine ⟨(t / X y) • y, ?_⟩
      change X ((t / X y) • y) = t
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hdy.ne']
    have hbelow (Y : E →L[ℝ] ℝ) (hY : Function.Surjective Y) (z : E)
        (hz : ∀ i : Fin m, Y z < Y (r i)) : z ∈ polygonExterior r := by
      have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
        ⟨⟨0, by dsimp [m]; omega⟩, Finset.mem_univ _⟩
      obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => Y (r i)) hne
      exact polygonExterior_of_lt_vertex_bound r Y hY (Y (r i))
        (fun k => hmin k (Finset.mem_univ k)) (hz i)
    have hleft : p 0 ∈ polygonExterior r := hbelow Xc hsurj (p 0) (by
      intro i
      rw [hri]
      exact (hX (c i) (hcA i).1.1 (hcA i).1.2.1).1)
    have hnsurj : Function.Surjective (-Xc) := by
      intro t
      obtain ⟨z, hz⟩ := hsurj (-t)
      refine ⟨z, ?_⟩
      change -Xc z = t
      rw [hz, neg_neg]
    have hright : p (Fin.last (n + 1)) ∈ polygonExterior r :=
      hbelow (-Xc) hnsurj (p (Fin.last (n + 1))) (by
        intro i
        change -Xc (p (Fin.last (n + 1))) < -Xc (r i)
        rw [neg_lt_neg_iff, hri]
        exact (hX (c i) (hcA i).1.1 (hcA i).1.2.1).2)
    refine ⟨j, hclose, hthree, c, r, fun _ => rfl, hre, hr,
      fun i => ⟨hcA i, hcnext i⟩, hedge, hcontact, hleft, hright, ?_⟩
    intro i
    let ip := (finRotate m).symm i
    let k := c i
    let l := c ip
    have hk : k ∈ B := (hcA i).1
    have hl : l ∈ B := (hcA ip).1
    have hgl : g l = k := by
      have hh := hcnext ip
      dsimp only [ip] at hh
      rw [Equiv.apply_symm_apply] at hh
      exact hh.symm
    have hincoming := hcand l hl
    rw [hgl] at hincoming
    obtain ⟨F, hFl, hFp, hFs, hk0, hkl, hklne, hkp, hks, hkT,
      hkpos1, hkpos2, hmin, _⟩ := hincoming
    have hheight := hp.normalized_minimal_candidate_neighbor_height l k F
      hl.1 hl.2.1 hk0 hkl hFl hFp hFs hklne hkp hks hkT hmin
    let H : E →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).toAffineMap.comp
      F.toAffineEquiv.toAffineMap
    have hHl : H (p l) < H (p k) := by
      change (F (p l)).1 + (F (p l)).2 < (F (p k)).1 + (F (p k)).2
      rw [hFl]
      simpa only [Prod.fst, Prod.snd, zero_add] using add_pos hkpos1 hkpos2
    obtain ⟨f, hfk, hfp, hfs, _, _, _, _, _, _, hjpos1, hjpos2, _⟩ := hcand k hk
    obtain ⟨U, hU, hiU, hUeq⟩ := exists_open_iUnion_eq_of_mem_imp
      (fun a : Fin m => r.edgeSet ℝ a)
      (fun a => (polygon_edgeSet_isCompact r a).isClosed) {ip, i} (r i) (by
        intro a ha
        rcases (hr.vertex_mem_edgeSet_iff i a).mp ha with hh | hh
        · exact Or.inr hh.symm
        · left
          apply (finRotate m).injective
          exact hh.symm.trans ((finRotate m).apply_symm_apply i).symm)
    have hipedge : r.edgeSet ℝ ip = segment ℝ (p k) (p l) := by
      rw [hedge]
      change segment ℝ (p l) (p (g l)) = _
      rw [hgl, segment_symm]
    have hiedge : r.edgeSet ℝ i = segment ℝ (p k) (p (g k)) := hedge i
    have hClocal (x : E) (hx : x ∈ U) :
        x ∈ r.boundary ℝ ↔ x ∈ segment ℝ (p k) (p l) ∪ segment ℝ (p k) (p (g k)) := by
      have hh := hUeq x hx
      change x ∈ r.boundary ℝ ↔ _ at hh
      rw [hh]
      constructor
      · rintro ⟨a, ha, hxa⟩
        rcases ha with rfl | rfl
        · exact Or.inl (hipedge ▸ hxa)
        · exact Or.inr (hiedge ▸ hxa)
      · rintro (hx' | hx')
        · exact ⟨ip, Or.inl rfl, hipedge.symm ▸ hx'⟩
        · exact ⟨i, Or.inr rfl, hiedge.symm ▸ hx'⟩
    obtain ⟨e, rho, eps, _, _, _, _, _, _, _, heps, _, hW, hkW, _, _,
      hCm, hCp, _, hcover, _, _, _, _, _, _, _, _, _, hrays⟩ :=
      exists_local_alternating_sides_at_arc_vertex hp k l (g k) hk.1 hk.2.1 f H
        hfk hfp hfs ⟨hjpos1, hjpos2⟩ hHl hheight.1 hheight.2
        (r.boundary ℝ) U univ hU (hri i ▸ hiU) hClocal isOpen_univ (mem_univ _)
    refine ⟨eps, heps, e ⁻¹' (Ioo (-rho) rho ×ˢ Ioo (-rho) rho),
      e ⁻¹' (Ioo (-rho) rho ×ˢ Ioo 0 rho), e ⁻¹' (Ioo (-rho) rho ×ˢ Ioo (-rho) 0),
      hW, (hri i).symm ▸ hkW, hCp.isPreconnected, hCm.isPreconnected, ?_, ?_, ?_⟩
    · rw [union_comm]
      exact hcover
    · intro t ht
      rw [hri]
      exact (hrays t ht).1
    · intro t ht
      rw [hri]
      exact (hrays t ht).2.1

end PoincareConjecture.M25.Topology3D
