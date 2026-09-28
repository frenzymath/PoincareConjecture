import PoincareConjecture.Proofs.M76.Wall.Mathlib.OrderedIntervalComplex
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FullArcDualContacts
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcDualBoundaryAvoidance
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteSubcomplexContact
import Mathlib.Order.Fin.Tuple












set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1

open Classical in




theorem exists_original_signed_tube_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K A Fr : SimplicialComplex ℝ E) [Fintype K.faces]
    (hAK : A ≤ K) (hFrK : Fr ≤ K)
    (hfullA : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    (hfullFr : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ Fr.vertices) → s ∈ Fr.faces)
    (b : I ≃ₜ A.space)
    (hcontact : A.space ∩ Fr.space =
      {(b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E),
        (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E)}) :
    ∃ (n : ℕ) (p : Fin (n + 2) → E) (v : Fin (n + 2) → I)
      (t : Fin (n + 3) → I),
      Function.Injective p ∧ StrictMono v ∧ StrictMono t ∧
      v 0 = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ ∧
      v (Fin.last (n + 1)) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ ∧
      t 0 = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ ∧
      t (Fin.last (n + 2)) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ ∧
      (∀ i, (b (v i) : E) = p i) ∧ A.vertices = range p ∧
      (∀ i : Fin (n + 1), {p i.castSucc, p i.succ} ∈ A.faces) ∧
      A.space = ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ) ∧
      (∀ i : Fin (n + 1),
        v i.castSucc < t i.castSucc.succ ∧ t i.castSucc.succ < v i.succ ∧
        (b (t i.castSucc.succ) : E) =
          ({p i.castSucc, p i.succ} : Finset E).centroid ℝ id) ∧
      (∀ i : Fin (n + 1),
        (K.barycentricDualBlock {p i.castSucc}).space ∩
            (K.barycentricDualBlock {p i.succ}).space =
          (K.barycentricDualBlock {p i.castSucc, p i.succ}).space) ∧
      (∀ i j : Fin (n + 2), i.val + 1 < j.val →
        Disjoint (K.barycentricDualBlock {p i}).space
          (K.barycentricDualBlock {p j}).space) ∧
      (∀ i j : Fin (n + 1), i ≠ j →
        Disjoint (K.barycentricDualBlock {p i.castSucc, p i.succ}).space
          (K.barycentricDualBlock {p j.castSucc, p j.succ}).space) ∧
      ∀ i : Fin (n + 1),
        Disjoint (K.barycentricDualBlock {p i.castSucc, p i.succ}).space Fr.space ∧
        ∃ q ∈ ({p i.castSucc, p i.succ} : Finset E), q ∉ Fr.vertices := by
  classical
  have hA : A.faces.Finite := (Set.toFinite K.faces).subset hAK
  have hfinite : (A.space ∩ Fr.space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hzero : (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E) ∈ A.vertices := by
    apply (mem_vertices_of_finite_subcomplex_intersection hAK hFrK hfinite
      (b ⟨0, ⟨le_rfl, zero_le_one⟩⟩).property ?_).1
    exact (hcontact.symm.subset (mem_insert _ _)).2
  have hone : (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E) ∈ A.vertices := by
    apply (mem_vertices_of_finite_subcomplex_intersection hAK hFrK hfinite
      (b ⟨1, ⟨zero_le_one, le_rfl⟩⟩).property ?_).1
    exact (hcontact.symm.subset (mem_insert_of_mem _ (mem_singleton _))).2
  obtain ⟨n, p, hp, hp0, hp1, hedge, hcover, hvertices⟩ :=
    A.exists_ordered_edge_chain_of_interval hA b hzero hone
  have hvertex (i : Fin (n + 2)) : p i ∈ A.vertices :=
    hvertices.symm.subset (mem_range_self i)
  have hpoint (i : Fin (n + 2)) : p i ∈ A.space := A.vertices_subset_space (hvertex i)
  have hne (i : Fin (n + 1)) : i.castSucc ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hsegments (i j : Fin (n + 1)) :
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩
          {p j.castSucc, p j.succ}) := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      A.inter_subset_convexHull (hedge i) (hedge j)
  have hlabels (i : Fin (n + 2)) :
      ∃ j : Fin (n + 1), i = j.castSucc ∨ i = j.succ := by
    by_cases hi : i.val = 0
    · exact ⟨0, Or.inl (Fin.ext hi)⟩
    · exact ⟨⟨i.val - 1, by omega⟩, Or.inr (Fin.ext (by simp; omega))⟩
  have hreal : Function.Injective (fun i : Fin (n + 2) => (i.val : ℝ)) := by
    intro i j hij
    exact Fin.ext (Nat.cast_injective hij)
  have hrealInter (i j : Fin (n + 1)) :
      segment ℝ (i.castSucc.val : ℝ) i.succ.val ∩
        segment ℝ (j.castSucc.val : ℝ) j.succ.val ⊆
          convexHull ℝ (({(i.castSucc.val : ℝ), (i.succ.val : ℝ)} : Set ℝ) ∩
            {(j.castSucc.val : ℝ), (j.succ.val : ℝ)}) := by
    simpa only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
      nat_unit_segments_inter i.val j.val
  have hsource : (⋃ i : Fin (n + 1),
      segment ℝ (i.castSucc.val : ℝ) (i.succ.val : ℝ)) = Icc 0 (n + 1 : ℝ) := by
    simpa only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
      iUnion_nat_unit_segments n
  obtain ⟨f, e, _he, hfv, hef⟩ := exists_finitePL_segment_correspondence
    (fun i : Fin (n + 1) => i.castSucc) (fun i => i.succ) hne hlabels
    (fun i : Fin (n + 2) => (i.val : ℝ)) p hreal hp hrealInter hsegments
  let Emap : Icc (0 : ℝ) (n + 1) ≃ₜ A.space :=
    (Homeomorph.setCongr hsource.symm).trans (e.trans (Homeomorph.setCongr hcover.symm))
  have hbound (i : Fin (n + 2)) : (i.val : ℝ) ∈ Icc 0 (n + 1 : ℝ) := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    exact_mod_cast (show i.val ≤ n + 1 by omega)
  have hE (i : Fin (n + 2)) : (Emap ⟨i.val, hbound i⟩ : E) = p i :=
    (hef _).trans (hfv i)
  let gamma := Emap.trans b.symm
  let v : Fin (n + 2) → I := fun i => b.symm ⟨p i, hpoint i⟩
  have hgamma (i : Fin (n + 2)) : gamma ⟨i.val, hbound i⟩ = v i := by
    apply congrArg b.symm
    exact Subtype.ext (hE i)
  have hv0 : v 0 = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ := by
    apply b.injective
    exact Subtype.ext ((congrArg Subtype.val (b.apply_symm_apply _)).trans hp0)
  have hv1 : v (Fin.last (n + 1)) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ := by
    apply b.injective
    exact Subtype.ext ((congrArg Subtype.val (b.apply_symm_apply _)).trans hp1)
  let : Fact ((0 : ℝ) ≤ n + 1) := ⟨by positivity⟩
  have hgamma0 : gamma ⊥ = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ := by
    convert (hgamma 0).trans hv0 using 1
    congr 1
    apply Subtype.ext
    simp
  have hgamma1 : gamma ⊤ = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ := by
    convert (hgamma (Fin.last (n + 1))).trans hv1 using 1
    congr 1
    apply Subtype.ext
    simp
  have hgammaMono : StrictMono gamma :=
    gamma.continuous.strictMono_of_inj_boundedOrder
      (by rw [hgamma0, hgamma1]; exact zero_le_one) gamma.injective
  have hv : StrictMono v := by
    intro i j hij
    rw [← hgamma i, ← hgamma j]
    apply hgammaMono
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  have hval (i : Fin (n + 2)) : (b (v i) : E) = p i :=
    congrArg Subtype.val (b.apply_symm_apply _)
  have hsegA (i : Fin (n + 1)) :
      segment ℝ (p i.castSucc) (p i.succ) ⊆ A.space := by
    simpa only [Finset.coe_pair, convexHull_pair] using A.convexHull_subset_space (hedge i)
  let line (i : Fin (n + 1)) : I → A.space := fun x =>
    ⟨AffineMap.lineMap (p i.castSucc) (p i.succ) (x : ℝ),
      hsegA i (lineMap_mem_segment ℝ _ _ x.property)⟩
  have hlinec (i : Fin (n + 1)) : Continuous (line i) :=
    ((ContinuousAffineMap.lineMap (p i.castSucc) (p i.succ)).continuous.comp
      continuous_subtype_val).subtype_mk _
  have hlinei (i : Fin (n + 1)) : Function.Injective (line i) := by
    intro x y hxy
    exact Subtype.ext ((AffineMap.lineMap_injective ℝ (hp.ne (hne i)))
      (congrArg Subtype.val hxy))
  have hl0 (i : Fin (n + 1)) : line i ⊥ = b (v i.castSucc) := by
    apply Subtype.ext
    rw [hval]
    exact AffineMap.lineMap_apply_zero _ _
  have hl1 (i : Fin (n + 1)) : line i ⊤ = b (v i.succ) := by
    apply Subtype.ext
    rw [hval]
    exact AffineMap.lineMap_apply_one _ _
  have hlineMono (i : Fin (n + 1)) : StrictMono (b.symm ∘ line i) := by
    apply (b.symm.continuous.comp (hlinec i)).strictMono_of_inj_boundedOrder
      _ (b.symm.injective.comp (hlinei i))
    simp only [Function.comp_apply, hl0, hl1, b.symm_apply_apply]
    exact (hv Fin.castSucc_lt_succ).le
  let middle : I := ⟨1 / 2, by constructor <;> norm_num⟩
  let mu : Fin (n + 1) → I := fun i => b.symm (line i middle)
  have hmu (i : Fin (n + 1)) : v i.castSucc < mu i ∧ mu i < v i.succ := by
    have hlo := hlineMono i (a := ⊥) (b := middle)
      (show (⊥ : I) < middle by change (0 : ℝ) < 1 / 2; norm_num)
    have hhi := hlineMono i (a := middle) (b := ⊤)
      (show middle < (⊤ : I) by change (1 / 2 : ℝ) < 1; norm_num)
    simpa only [Function.comp_apply, hl0, hl1, b.symm_apply_apply, mu] using And.intro hlo hhi
  have hmuMono : StrictMono mu := by
    intro i j hij
    exact ((hmu i).2.trans_le (hv.monotone
      (show i.succ ≤ j.castSucc by change i.val + 1 ≤ j.val; omega))).trans (hmu j).1
  have hmu0 (i : Fin (n + 1)) : (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I) < mu i := by
    rw [← hv0]
    exact (hv.monotone (Fin.zero_le _)).trans_lt (hmu i).1
  have hmu1 (i : Fin (n + 1)) : mu i < (⟨1, ⟨zero_le_one, le_rfl⟩⟩ : I) := by
    rw [← hv1]
    exact (hmu i).2.trans_le (hv.monotone (Fin.le_last _))
  let tail : Fin (n + 2) → I := Fin.snoc mu ⟨1, ⟨zero_le_one, le_rfl⟩⟩
  have htail : StrictMono tail := by
    change StrictMono (Fin.snoc mu (⟨1, ⟨zero_le_one, le_rfl⟩⟩ : I))
    rw [← Fin.insertNth_last', Fin.strictMono_insertNth_iff]
    exact ⟨hmuMono, fun i _ => hmu1 i, fun i hi => False.elim
      (not_le_of_gt (Fin.castSucc_lt_last i) hi)⟩
  have htail0 (i : Fin (n + 2)) : (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I) < tail i := by
    induction i using Fin.lastCases with
    | last =>
      simpa only [tail, Fin.snoc_last] using
        (show (⟨0, ⟨le_rfl, zero_le_one⟩⟩ : I) < ⟨1, ⟨zero_le_one, le_rfl⟩⟩
          from zero_lt_one)
    | cast i => simpa only [tail, Fin.snoc_castSucc] using hmu0 i
  let t : Fin (n + 3) → I := Fin.cons ⟨0, ⟨le_rfl, zero_le_one⟩⟩ tail
  have ht : StrictMono t := Fin.strictMono_cons.mpr ⟨htail0, htail⟩
  have ht0 : t 0 = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ := Fin.cons_zero _ _
  have ht1 : t (Fin.last (n + 2)) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ := by
    change Fin.cons (α := fun _ => I) _ tail _ = _
    rw [show Fin.last (n + 2) = (Fin.last (n + 1)).succ from Fin.ext (by simp)]
    rw [Fin.cons_succ]
    exact Fin.snoc_last _ _
  have htm (i : Fin (n + 1)) : t i.castSucc.succ = mu i := by
    simp only [t, tail, Fin.cons_succ, Fin.snoc_castSucc]
  have hmid (i : Fin (n + 1)) : (b (mu i) : E) =
      ({p i.castSucc, p i.succ} : Finset E).centroid ℝ id := by
    rw [show (b (mu i) : E) = (line i middle : E) from
      congrArg Subtype.val (b.apply_symm_apply _)]
    change AffineMap.lineMap (p i.castSucc) (p i.succ) (1 / 2 : ℝ) = _
    simp only [Finset.centroid_pair, AffineMap.lineMap_apply, one_div, id_eq]
  obtain ⟨hjoint, _hlinks, hfar, hdisjoint⟩ :=
    K.full_arc_dual_contacts A hAK hfullA p hp hvertex hedge hcover
  refine ⟨n, p, v, t, hp, hv, ht, hv0, hv1, ht0, ht1, hval, hvertices,
    hedge, hcover, ?_, hjoint, hfar, hdisjoint, ?_⟩
  · intro i
    rw [htm]
    exact ⟨(hmu i).1, (hmu i).2, hmid i⟩
  · intro i
    apply K.arc_edge_dual_disjoint_boundary A Fr hAK hFrK hfullFr hfinite (hedge i)
    exact Finset.card_pair (hp.ne (hne i))

end PoincareConjecture.M76.Dehn
