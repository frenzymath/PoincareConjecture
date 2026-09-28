import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeOrder
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricBoundaryFacetInterval
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualFacetInterval
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1

open Classical in




theorem exists_original_signed_tube_axis_maps
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K A Fr : SimplicialComplex ℝ E) [Fintype K.faces]
    (hAK : A ≤ K) (hFrK : Fr ≤ K)
    (hfullA : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    (hfullFr : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ Fr.vertices) → s ∈ Fr.faces)
    (b : I ≃ₜ A.space) (hb : b.IsFinitePL)
    (hcontact : A.space ∩ Fr.space =
      {(b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E),
        (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E)}) :
    ∃ (n : ℕ) (p : Fin (n + 2) → E) (t : Fin (n + 3) → I)
      (hsub : ∀ i : Fin (n + 2), Icc (t i.castSucc : ℝ) (t i.succ : ℝ) ⊆ I),
      Function.Injective p ∧ StrictMono t ∧
      t 0 = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ ∧
      t (Fin.last (n + 2)) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ ∧
      A.vertices = range p ∧
      (∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ A.faces) ∧
      A.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ) ∧
      (∀ i : Fin (n + 1), (b (t i.castSucc.succ) : E) =
        ({p i.castSucc, p i.succ} : Finset E).centroid ℝ id) ∧
      ∀ i : Fin (n + 2),
        ∃ axis : Icc (t i.castSucc : ℝ) (t i.succ : ℝ) ≃ₜ
          ↥((K.barycentricDualBlock {p i}).space ∩ A.space),
          axis.IsFinitePL ∧ ∀ x, (axis x : E) = (b ⟨x, hsub i x.property⟩ : E) := by
  classical
  obtain ⟨n, p, v, t, hp, _hv, ht, hv0, hv1, ht0, ht1, hval, hverts,
    hedge, hcover, hmid, _hjoint, _hfar, _hdisjoint, _havoid⟩ :=
    exists_original_signed_tube_order K A Fr hAK hFrK hfullA hfullFr b hcontact
  have hA : A.faces.Finite := (Set.toFinite K.faces).subset hAK
  let : Fintype A.faces := hA.fintype
  have hvertex (i : Fin (n + 2)) : p i ∈ A.vertices :=
    hverts.symm.subset (mem_range_self i)
  have hne (i : Fin (n + 1)) : p i.castSucc ≠ p i.succ := by
    apply hp.ne
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  have hcard : ∀ s ∈ A.faces, s.card ≤ 2 := by
    intro s hs
    obtain ⟨_, i, hsi⟩ := (A.faces_of_edge_chain_cover p hedge hcover s).mp hs
    exact (Finset.card_le_card hsi).trans (by rw [Finset.card_pair (hne i)])
  have hcoface (i : Fin (n + 2)) (s : Finset E) (hs : s ∈ A.faces)
      (hps : {p i} ⊆ s) (hsc : s.card = 2) :
      ∃ j : Fin (n + 1), s = {p j.castSucc, p j.succ} ∧
        (i = j.castSucc ∨ i = j.succ) := by
    obtain ⟨_, j, hsj⟩ := (A.faces_of_edge_chain_cover p hedge hcover s).mp hs
    have he : s = {p j.castSucc, p j.succ} :=
      Finset.eq_of_subset_of_card_le hsj (by rw [hsc, Finset.card_pair (hne j)])
    refine ⟨j, he, ?_⟩
    have hmem := hsj (hps (Finset.mem_singleton_self (p i)))
    simpa only [Finset.mem_insert, Finset.mem_singleton, hp.eq_iff] using hmem
  have hp0 : p 0 = (b (t 0) : E) := by
    rw [ht0, ← hv0]
    exact (hval 0).symm
  have hp1 : p (Fin.last (n + 1)) = (b (t (Fin.last (n + 2))) : E) := by
    rw [ht1, ← hv1]
    exact (hval (Fin.last (n + 1))).symm
  let Z (i : Fin (n + 2)) := (K.barycentricDualBlock {p i}).space ∩ A.space
  have hZ (i : Fin (n + 2)) : IsFinitePLBallPair ℝ (Z i)
      {(b (t i.castSucc) : E), (b (t i.succ) : E)} := by
    change IsFinitePLBallPair ℝ ((K.barycentricDualBlock {p i}).space ∩ A.space) _
    rw [K.barycentricDualBlock_space_inter_subcomplex A hAK]
    by_cases hi0 : i = 0
    · subst i
      have hco : ∀ s ∈ A.faces, {p 0} ⊆ s → s.card = 2 →
          s = {p (0 : Fin (n + 1)).castSucc, p (0 : Fin (n + 1)).succ} := by
        intro s hs hps hsc
        obtain ⟨j, rfl, hj⟩ := hcoface 0 s hs hps hsc
        have hj0 : j = 0 := by
          apply Fin.ext
          change j.val = 0
          rcases hj with hj | hj
          · have hv : 0 = j.val := congrArg Fin.val hj
            omega
          · have hv : 0 = j.val + 1 := congrArg Fin.val hj
            omega
        rw [hj0]
      have hball := (A.barycentricDualBlock_of_single_coface hcard (hvertex 0)
        (hedge 0) (Finset.card_singleton _) (Finset.card_pair (hne 0))
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) hco).2.1
      simp only [Finset.centroid_singleton, id_eq] at hball
      rw [← (hmid 0).2.2] at hball
      simpa only [hp0, Fin.castSucc_zero] using hball
    by_cases hilast : i = Fin.last (n + 1)
    · subst i
      let j : Fin (n + 1) := Fin.last n
      have hjright : j.succ = Fin.last (n + 1) := Fin.ext (by simp [j])
      have hjtime : j.castSucc.succ = (Fin.last (n + 1)).castSucc := Fin.ext (by simp [j])
      have hco : ∀ s ∈ A.faces, {p (Fin.last (n + 1))} ⊆ s → s.card = 2 →
          s = {p j.castSucc, p j.succ} := by
        intro s hs hps hsc
        obtain ⟨k, rfl, hk⟩ := hcoface _ s hs hps hsc
        have hkj : k = j := by
          apply Fin.ext
          rcases hk with hk | hk <;> have hv := congrArg Fin.val hk <;>
            simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ] at hv <;>
            have hbnd := k.isLt <;> change k.val = n <;> omega
        rw [hkj]
      have hsubedge : ({p (Fin.last (n + 1))} : Finset E) ⊆
          {p j.castSucc, p j.succ} := by
        rw [← hjright]
        exact Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hball := (A.barycentricDualBlock_of_single_coface hcard (hvertex _)
        (hedge j) (Finset.card_singleton _) (Finset.card_pair (hne j)) hsubedge hco).2.1
      have hlasttime : (Fin.last (n + 1)).succ = Fin.last (n + 2) := Fin.ext rfl
      simpa only [Finset.centroid_singleton, id_eq, hp1, ← (hmid j).2.2, hjtime,
        hlasttime, Set.pair_comm (b (t (Fin.last (n + 2))) : E)] using hball
    · have hiPos : 0 < i.val := by
        by_contra hn
        apply hi0
        apply Fin.ext
        change i.val = 0
        omega
      have hiLast : i.val < n + 1 := by
        by_contra hn
        apply hilast
        apply Fin.ext
        change i.val = n + 1
        have hiBound := i.isLt
        omega
      let j : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      let k : Fin (n + 1) := ⟨i.val, hiLast⟩
      have hj : j.succ = i := Fin.ext (by simp [j]; omega)
      have hk : k.castSucc = i := Fin.ext rfl
      have hjtime : j.castSucc.succ = i.castSucc := Fin.ext (by simp [j]; omega)
      have hktime : k.castSucc.succ = i.succ := Fin.ext rfl
      have hco : ∀ s ∈ A.faces, {p i} ⊆ s → s.card = 2 →
          s = {p j.castSucc, p j.succ} ∨ s = {p k.castSucc, p k.succ} := by
        intro s hs hps hsc
        obtain ⟨l, rfl, hl⟩ := hcoface i s hs hps hsc
        rcases hl with hl | hl
        · right
          have hlk : l = k := Fin.ext (congrArg Fin.val hl).symm
          rw [hlk]
        · left
          have hlj : l = j := by
            apply Fin.ext
            have hv := congrArg Fin.val hl
            change i.val = l.val + 1 at hv
            change l.val = i.val - 1
            omega
          rw [hlj]
      have hjk : ({p j.castSucc, p j.succ} : Finset E) ≠ {p k.castSucc, p k.succ} := by
        intro he
        have hmem : p j.castSucc ∈ ({p k.castSucc, p k.succ} : Finset E) :=
          he ▸ Finset.mem_insert_self _ _
        simp only [Finset.mem_insert, Finset.mem_singleton, hp.eq_iff] at hmem
        rcases hmem with h | h <;> have hv := congrArg Fin.val h <;>
          simp only [Fin.val_castSucc, Fin.val_succ] at hv <;>
          change i.val - 1 = _ at hv <;> dsimp only [k] at hv <;> omega
      have hball := (A.isFinitePLBallPair_barycentricDualBlock_of_paired_facet
        hcard (hvertex i) (hedge j) (hedge k) (Finset.card_singleton _)
        (Finset.card_pair (hne j)) (Finset.card_pair (hne k))
        (Finset.singleton_subset_iff.mpr (by rw [← hj]; simp))
        (Finset.singleton_subset_iff.mpr (by rw [← hk]; simp)) hjk hco).1
      simpa only [← (hmid j).2.2, ← (hmid k).2.2, hjtime, hktime] using hball
  have hsub (i : Fin (n + 2)) : Icc (t i.castSucc : ℝ) (t i.succ : ℝ) ⊆ I :=
    Icc_subset_Icc (t i.castSucc).property.1 (t i.succ).property.2
  refine ⟨n, p, t, hsub, hp, ht, ht0, ht1, hverts, hedge, hcover,
    fun i => (hmid i).2.2, ?_⟩
  intro i
  have hlt : t i.castSucc < t i.succ := ht Fin.castSucc_lt_succ
  have hends : (b (t i.castSucc) : E) ≠ (b (t i.succ) : E) :=
    fun he => hlt.ne (b.injective (Subtype.ext he))
  obtain ⟨q, _hq, hq0, hq1⟩ := (hZ i).exists_unitInterval_chart_with_endpoints hends
  let inc : Z i → A.space := fun z => ⟨z, z.property.2⟩
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk (fun z => z.property.2)
  let phi : I → ℝ := fun x => (b.symm (inc (q x)) : ℝ)
  have hphi : Continuous phi := continuous_subtype_val.comp
    (b.symm.continuous.comp (hinc.comp q.continuous))
  have hphi0 : phi ⊥ = (t i.castSucc : ℝ) := by
    change (b.symm (inc (q ⊥)) : ℝ) = _
    have he : inc (q ⊥) = b (t i.castSucc) := Subtype.ext hq0
    rw [he, b.symm_apply_apply]
  have hphi1 : phi ⊤ = (t i.succ : ℝ) := by
    change (b.symm (inc (q ⊤)) : ℝ) = _
    have he : inc (q ⊤) = b (t i.succ) := Subtype.ext hq1
    rw [he, b.symm_apply_apply]
  have hphii : Function.Injective phi := by
    intro x y he
    apply q.injective
    have he' := b.symm.injective (Subtype.ext he)
    exact Subtype.ext (show (q x : E) = (q y : E) from
      congrArg (fun z : A.space => (z : E)) he')
  have hmono : StrictMono phi := hphi.strictMono_of_inj_boundedOrder
    (by rw [hphi0, hphi1]; exact hlt.le) hphii
  have himage : range phi = Icc (t i.castSucc : ℝ) (t i.succ : ℝ) := by
    have h := hphi.continuousOn.image_Icc_of_monotoneOn (show (⊥ : I) ≤ ⊤ from bot_le)
      (hmono.monotone.monotoneOn _)
    simpa only [Icc_bot_top, image_univ, hphi0, hphi1] using h
  have hmem (x : I) : (x : ℝ) ∈ Icc (t i.castSucc : ℝ) (t i.succ : ℝ) ↔
      (b x : E) ∈ Z i := by
    rw [← himage]
    constructor
    · rintro ⟨y, hy⟩
      have he : b.symm (inc (q y)) = x := Subtype.ext hy
      have hbval : (q y : E) = (b x : E) := by
        have hv := congrArg b he
        rw [b.apply_symm_apply] at hv
        exact congrArg Subtype.val hv
      exact hbval ▸ (q y).property
    · intro hx
      obtain ⟨y, hy⟩ := q.surjective ⟨b x, hx⟩
      refine ⟨y, ?_⟩
      change (b.symm (inc (q y)) : ℝ) = x
      rw [hy]
      exact congrArg Subtype.val (b.symm_apply_apply x)
  let axis := b.restrictSubsets (hsub i) (show Z i ⊆ A.space from inter_subset_right) hmem
  have hI := isFinitePLBallPair_Icc (show (t i.castSucc : ℝ) < (t i.succ : ℝ) from hlt)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ := hI
  exact ⟨axis, hb.restrictSubsets (hsub i) inter_subset_right hmem L hL hLs, fun _ => rfl⟩

end PoincareConjecture.M76.Dehn
