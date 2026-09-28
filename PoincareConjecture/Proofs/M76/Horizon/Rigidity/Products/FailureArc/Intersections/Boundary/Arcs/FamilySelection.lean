import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Arcs.Outermost
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.OneMarkedEnd



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_outermost_returning_disk_of_interval_family
    {κ : Type*} [Finite κ] {H T : Set P2}
    (hH : IsFinitePLBallPair P2 H (frontier H))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hHT : H ⊆ interior T)
    (pieces : κ → Set P2)
    (hsub : ∀ i, pieces i ⊆ T \ interior H)
    (hdis : Pairwise (fun i j ↦ Disjoint (pieces i) (pieces j)))
    (hball : ∀ i, IsFinitePLBallPair ℝ (pieces i)
      (pieces i ∩ (frontier H ∪ frontier T)))
    (a : P2) (hfirst : (⋃ i, pieces i) ∩ frontier H = {a})
    (hreturn : ∃ i, Disjoint (pieces i) (frontier H)) :
    ∃ (i : κ) (D B U V : Set P2),
      IsFinitePLBallPair P2 D (U ∪ pieces i) ∧
      IsFinitePLBallPair P2 B (pieces i ∪ V) ∧
      IsFinitePLBallPair ℝ U (U ∩ pieces i) ∧
      D ∪ B = T ∧ D ∩ B = pieces i ∧
      D ∩ frontier T = U ∧ B ∩ frontier T = V ∧
      H ⊆ interior B ∧ Disjoint D H ∧ D ⊆ T \ H ∧
      D ∩ (⋃ j, pieces j) = pieces i := by
  classical
  have hrims : Disjoint (frontier H) (frontier T) := by
    refine disjoint_left.mpr fun x hxH hxT ↦ ?_
    exact hxT.2 (hHT (hH.1 hxH))
  obtain ⟨s, b, ha, hb, _, hs, _, _, _, _, hothers⟩ :=
    exists_unique_spanning_interval_of_one_marked_point pieces (frontier H) (frontier T)
      a hrims hdis hfirst (fun i ↦ Or.inl (hball i))
  let I := {i : κ // i ≠ s}
  have hI : Nonempty I := by
    obtain ⟨i, hi⟩ := hreturn
    refine ⟨⟨i, ?_⟩⟩
    intro his
    exact disjoint_left.mp hi (his.symm ▸ hs.1 (Or.inl rfl)) ha
  letI : Nonempty I := hI
  have hmodels (i : I) : IsFinitePLBallPair ℝ (pieces i) (pieces i ∩ frontier T) :=
    (hothers i i.property).2.1 ▸ hball i
  choose u v huv hends using fun i : I ↦ (hmodels i).exists_boundary_eq_pair
  have hWball (i : I) : IsFinitePLBallPair ℝ (pieces i) {u i, v i} := hends i ▸ hmodels i
  have hu (i : I) : u i ∈ frontier T := ((hends i).superset (Or.inl rfl)).2
  have hv (i : I) : v i ∈ frontier T := ((hends i).superset (Or.inr rfl)).2
  have hproper (i : I) : pieces i \ {u i, v i} ⊆ interior T := by
    rw [hT.interior_eq_sdiff_of_finrank_eq rfl]
    exact fun x hx ↦ ⟨(hsub i hx.1).1, fun hq ↦ hx.2 ((hends i).subset ⟨hx.1, hq⟩)⟩
  have havoidH (i : I) : Disjoint (pieces i) H := by
    refine disjoint_left.mpr fun x hx hxH ↦ ?_
    exact disjoint_left.mp (hothers i i.property).1 hx
      ⟨subset_closure hxH, (hsub i hx).2⟩
  have hdisI : Pairwise (fun i j : I ↦ Disjoint (pieces i) (pieces j)) :=
    fun i j hij ↦ hdis (fun heq ↦ hij (Subtype.ext heq))
  obtain ⟨i, D, B, U, V, hU, _, _, _, hD, hB, hcover, hcommon, hDU, hBV,
    hHin, hDH, hDT, havoid, hspan⟩ :=
    exists_outermost_returning_arc_disk (fun i : I ↦ pieces i) u v hH hT hHT
      hWball huv hu hv hproper havoidH hdisI
  have hSpanDis : Disjoint D (pieces s) := by
    exact hspan (pieces s) hs.isConnected.isPreconnected
      (fun x hx ↦ (hsub s hx).1) (hdis i.property.symm)
      ⟨a, hs.1 (Or.inl rfl), hH.1 ha⟩
  have htotal : D ∩ (⋃ j, pieces j) = pieces i := by
    apply Subset.antisymm
    · rintro x ⟨hxD, hxall⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxall
      by_cases hjs : j = s
      · exact (disjoint_left.mp hSpanDis hxD (hjs ▸ hxj)).elim
      · let j' : I := ⟨j, hjs⟩
        by_cases hji : j' = i
        · exact congrArg Subtype.val hji ▸ hxj
        · exact (disjoint_left.mp (havoid j' hji) hxD hxj).elim
    · intro x hx
      exact ⟨(hcommon.superset hx).1, mem_iUnion.mpr ⟨i, hx⟩⟩
  have hUcontact : U ∩ pieces i = {u i, v i} := by
    apply Subset.antisymm
    · intro x hx
      exact (hends i).subset ⟨hx.2, (hDU.superset hx.1).2⟩
    · intro x hx
      exact ⟨hU.1 hx, (hWball i).1 hx⟩
  exact ⟨i, D, B, U, V, hD, hB, hUcontact.symm ▸ hU, hcover, hcommon,
    hDU, hBV, hHin, hDH, hDT, htotal⟩

end PoincareConjecture.M76.Dehn.Annuli
