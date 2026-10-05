import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.FinitePLDiskAttachment
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.FinitePLProperArcCut
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.PunctureBallTriangulation

/-! # Outermost disk surgery with a nonextendable rim

Cut the actual disk along the proper shared arc and attach the actual
outermost disk to each piece. A common endpoint-fixed interval map
constructs matching boundary reparametrizations. If both new rims
extended into the prescribed boundary target, the two extensions would
paste to an extension of the original rim.

This is the outermost-arc compression step used in relative handle
addition (Hamilton 1976, p. 67; Wu, A Generalization of the Handle
Addition Theorem, proof of Theorem 1, assertion (2)).
-/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76

/-- Construct both literal surgery disks, retaining their whole rims,
proper frontier contacts and complete common disk. -/
theorem exists_outermost_disk_surgery
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C q D W V M F : Set E} {a b : E}
    (hC : IsFinitePLBallPair (ℝ × ℝ) C q)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (V ∪ W))
    (hW : IsFinitePLBallPair ℝ W {a,b}) (hV : IsFinitePLBallPair ℝ V {a,b})
    (ha : a ∈ q) (hb : b ∈ q) (hab : a ≠ b)
    (hproper : W \ {a,b} ⊆ C \ q) (hVW : V ∩ W = {a,b})
    (hCD : C ∩ D = W) (hCM : C ⊆ M) (hDM : D ⊆ M)
    (hCF : C ∩ F = q) (hDF : D ∩ F = V) :
    ∃ A U : Bool → Set E,
      (∀ i, IsFinitePLBallPair ℝ (U i) {a,b}) ∧
      (∀ i, IsFinitePLBallPair (ℝ × ℝ) (A i) (U i ∪ W)) ∧
      A false ∪ A true = C ∧ A false ∩ A true = W ∧
      U false ∪ U true = q ∧ U false ∩ U true = {a,b} ∧
      (∀ i, A i ∩ q = U i) ∧
      (∀ i, IsFinitePLBallPair (ℝ × ℝ) (A i ∪ D) (U i ∪ V)) ∧
      (∀ i, A i ∪ D ⊆ M) ∧ (∀ i, (A i ∪ D) ∩ F = U i ∪ V) ∧
      (A false ∪ D) ∩ (A true ∪ D) = D := by
  obtain ⟨U₀,U₁,hU₀,hU₁,hUq,hUi⟩ := hC.exists_boundary_arcs ha hb hab
  obtain ⟨A₀,A₁,hA₀,hA₁,hAC,hAi,hAq₀,hAq₁⟩ :=
    hC.exists_proper_arc_cut hU₀ hU₁ hW hab hUi.subset hUq hproper
  let A : Bool → Set E := fun i => if i then A₁ else A₀
  let U : Bool → Set E := fun i => if i then U₁ else U₀
  have hA (i : Bool) : IsFinitePLBallPair (ℝ × ℝ) (A i) (U i ∪ W) := by
    cases i
    · exact hA₀
    · simpa only [A,U,if_true,union_comm] using hA₁
  have hU (i : Bool) : IsFinitePLBallPair ℝ (U i) {a,b} := by
    cases i <;> assumption
  have hAC' (i : Bool) : A i ⊆ C := by
    cases i
    · exact subset_union_left.trans hAC.subset
    · exact subset_union_right.trans hAC.subset
  have hAq (i : Bool) : A i ∩ q = U i := by cases i <;> assumption
  have hWq : W ∩ q = {a,b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper ⟨hx.1,hn⟩).2 hx.2
    · intro x hx
      exact ⟨hW.1 hx,by rcases hx with rfl | rfl <;> assumption⟩
  have hUW (i : Bool) : U i ∩ W = {a,b} := by
    apply Subset.antisymm
    · exact fun x hx => hWq.subset ⟨hx.2,(hAq i).symm.subset hx.1 |>.2⟩
    · exact fun x hx => ⟨(hU i).1 hx,hW.1 hx⟩
  have hAD (i : Bool) : A i ∩ D = W := by
    apply Subset.antisymm
    · exact fun x hx => hCD.subset ⟨hAC' i hx.1,hx.2⟩
    · exact fun x hx => ⟨(hA i).1 (Or.inr hx),hD.1 (Or.inr hx)⟩
  have hAF (i : Bool) : A i ∩ F = U i := by
    rw [←hAq i]
    ext x
    constructor
    · exact fun hx => ⟨hx.1,hCF.subset ⟨hAC' i hx.1,hx.2⟩⟩
    · exact fun hx => ⟨hx.1,(hCF.symm.subset hx.2).2⟩
  refine ⟨A,U,hU,hA,hAC,hAi,hUq,hUi,hAq,?_,?_,?_,?_⟩
  · intro i
    exact (hA i).union_of_interval_attachment hD (hU i) hV hW (hUW i) hVW (hAD i)
  · exact fun i => union_subset ((hAC' i).trans hCM) hDM
  · intro i
    rw [union_inter_distrib_right,hAF i,hDF]
  · change (A₀ ∪ D) ∩ (A₁ ∪ D) = D
    rw [←inter_union_distrib_right,hAi]
    exact union_eq_right.mpr (fun _ hx => hD.1 (Or.inr hx))

private theorem exists_endpoint_fixed_arc_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W V q : Set E} (hW : IsFinitePLBallPair ℝ W q)
    (hV : IsFinitePLBallPair ℝ V q) :
    ∃ f : W ≃ₜ V, f.IsFinitePL ∧
      (∀ x : W, (x : E) ∈ q ↔ (f x : E) ∈ q) ∧
      ∀ x : W, (x : E) ∈ q → (f x : E) = x := by
  obtain ⟨_,K,_,_,hK,hKq⟩ := hW.exists_finite_carrier_and_rim_complexes
  have hid : (Homeomorph.refl q).IsFinitePL :=
    ⟨id,⟨K,hK,hKq,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,fun _ => rfl⟩
  obtain ⟨f,hf,hfix,hmem⟩ := hW.exists_extension hV (Homeomorph.refl q) hid
  refine ⟨f,hf,hmem,?_⟩
  intro x hx
  exact congrArg Subtype.val (hfix ⟨x,hx⟩)

private theorem exists_disk_boundary_arc_replacement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B U W V q : Set E}
    (hA : IsFinitePLBallPair (ℝ × ℝ) A (U ∪ W))
    (hB : IsFinitePLBallPair (ℝ × ℝ) B (U ∪ V))
    (hU : IsFinitePLBallPair ℝ U q) (hUW : U ∩ W = q) (hUV : U ∩ V = q)
    (f : W ≃ₜ V) (hf : f.IsFinitePL)
    (hfix : ∀ x : W, (x : E) ∈ q → (f x : E) = x) :
    ∃ H : A ≃ₜ B, H.IsFinitePL ∧
      (∀ x : U, (H ⟨x,hA.1 (Or.inl x.property)⟩ : E) = x) ∧
      ∀ x : W, (H ⟨x,hA.1 (Or.inr x.property)⟩ : E) = f x := by
  obtain ⟨K,_,hK,hKU,_,_⟩ := hU.exists_finite_carrier_and_rim_complexes
  have hid : (Homeomorph.refl U).IsFinitePL :=
    ⟨id,⟨K,hK,hKU,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,fun _ => rfl⟩
  obtain ⟨r,hr,hrU,hrW⟩ := Homeomorph.exists_union_finitePL (Homeomorph.refl U) f hid hf
    (fun x => by
      change (x : E) ∈ W ↔ (x : E) ∈ V
      have h₁ : (x : E) ∈ W ↔ (x : E) ∈ q := by
        rw [←hUW]; exact (and_iff_right x.property).symm
      have h₂ : (x : E) ∈ V ↔ (x : E) ∈ q := by
        rw [←hUV]; exact (and_iff_right x.property).symm
      exact h₁.trans h₂.symm)
    (fun x hxU hxW => (hfix ⟨x,hxW⟩ (hUW.subset ⟨hxU,hxW⟩)).symm)
  obtain ⟨H,hH,hHr,_⟩ := hA.exists_extension hB r hr
  refine ⟨H,hH,?_,?_⟩
  · intro x
    exact (congrArg Subtype.val (hHr ⟨x,Or.inl x.property⟩)).trans (hrU x)
  · intro x
    exact (congrArg Subtype.val (hHr ⟨x,Or.inr x.property⟩)).trans (hrW x)

private theorem exists_nonextendable_surgery_branch
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Y]
    {C q D W V z : Set E} (A U : Bool → Set E)
    (hC : IsFinitePLBallPair (ℝ × ℝ) C q)
    (hU : ∀ i, IsFinitePLBallPair ℝ (U i) z)
    (hA : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (A i) (U i ∪ W))
    (hcover : A false ∪ A true = C) (hinter : A false ∩ A true = W)
    (hUq : U false ∪ U true = q) (hAq : ∀ i, A i ∩ q = U i)
    (hnew : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (A i ∪ D) (U i ∪ V))
    (hW : IsFinitePLBallPair ℝ W z) (hV : IsFinitePLBallPair ℝ V z)
    (hUW : ∀ i, U i ∩ W = z) (hUV : ∀ i, U i ∩ V = z)
    (γ : E → Y)
    (hne : ¬ ∃ f : C(C,Y), ∀ x (hx : x ∈ q), f ⟨x,hC.1 hx⟩ = γ x) :
    ∃ i : Bool, ¬ ∃ f : C(↥(A i ∪ D),Y),
      ∀ x (hx : x ∈ U i ∪ V), f ⟨x,(hnew i).1 hx⟩ = γ x := by
  classical
  obtain ⟨φ,hφ,_,hφfix⟩ := exists_endpoint_fixed_arc_map hW hV
  choose H hH hHU hHW using fun i =>
    exists_disk_boundary_arc_replacement (hA i) (hnew i) (hU i)
      (hUW i) (hUV i) φ hφ hφfix
  by_contra hn
  push Not at hn
  choose f hf using hn
  have hAC (i : Bool) : A i ⊆ C := by
    cases i
    · exact subset_union_left.trans hcover.subset
    · exact subset_union_right.trans hcover.subset
  have hfW (i : Bool) (x : W) :
      f i (H i ⟨x,(hA i).1 (Or.inr x.property)⟩) = γ (φ x) := by
    have hxval := hHW i x
    have hxsub : H i ⟨x,(hA i).1 (Or.inr x.property)⟩ =
        ⟨φ x,(hnew i).1 (Or.inr (φ x).property)⟩ := Subtype.ext hxval
    rw [hxsub]
    exact hf i _ (Or.inr (φ x).property)
  have hagree (x : E) (hx₀ : x ∈ A false) (hx₁ : x ∈ A true) :
      f false (H false ⟨x,hx₀⟩) = f true (H true ⟨x,hx₁⟩) := by
    have hxW : x ∈ W := hinter.subset ⟨hx₀,hx₁⟩
    exact (hfW false ⟨x,hxW⟩).trans (hfW true ⟨x,hxW⟩).symm
  let g : C → Y := fun x => if hx : (x : E) ∈ A false then f false (H false ⟨x,hx⟩)
    else f true (H true ⟨x,(hcover.symm.subset x.property).resolve_left hx⟩)
  have hg (i : Bool) (x : C) (hx : (x : E) ∈ A i) : g x = f i (H i ⟨x,hx⟩) := by
    cases i
    · simp only [g,dif_pos hx]
    · dsimp only [g]
      split_ifs with h
      · exact hagree x h hx
      · rfl
  have hgc (i : Bool) : ContinuousOn g ((Subtype.val : C → E) ⁻¹' A i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : ((Subtype.val : C → E) ⁻¹' A i) → A i := fun x => ⟨x.val.val,x.property⟩
    have hj : Continuous j := by fun_prop
    exact ((f i).continuous.comp ((H i).continuous.comp hj)).congr
      (fun x => (hg i x.val x.property).symm)
  have hgcont : Continuous g := by
    have hh := (hgc false).union_of_isClosed (hgc true)
      ((hA false).isCompact.isClosed.preimage continuous_subtype_val)
      ((hA true).isCompact.isClosed.preimage continuous_subtype_val)
    have hwhole : ((Subtype.val : C → E) ⁻¹' A false) ∪
        ((Subtype.val : C → E) ⁻¹' A true) = univ := by
      rw [←preimage_union,hcover]
      ext x
      simp only [mem_preimage,x.property,mem_univ]
    rw [hwhole] at hh
    exact continuousOn_univ.mp hh
  apply hne
  refine ⟨⟨g,hgcont⟩,?_⟩
  intro x hx
  obtain ⟨i,hxi⟩ : ∃ i : Bool, x ∈ U i := by
    rcases hUq.symm.subset hx with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  change g ⟨x,hC.1 hx⟩ = _
  rw [hg i _ ((hAq i).symm.subset hxi).1]
  have hv := hHU i ⟨x,hxi⟩
  have hs : H i ⟨x,((hAq i).symm.subset hxi).1⟩ =
      ⟨x,(hnew i).1 (Or.inl hxi)⟩ := Subtype.ext hv
  rw [hs]
  exact hf i x (Or.inl hxi)

/-- At least one of the constructed surgery disks retains a rim which
does not extend into the boundary target. No branch is supplied. -/
theorem exists_essential_outermost_disk_surgery
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Y]
    {C q D W V M F : Set E} {a b : E}
    (hC : IsFinitePLBallPair (ℝ × ℝ) C q)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (V ∪ W))
    (hW : IsFinitePLBallPair ℝ W {a,b}) (hV : IsFinitePLBallPair ℝ V {a,b})
    (ha : a ∈ q) (hb : b ∈ q) (hab : a ≠ b)
    (hproper : W \ {a,b} ⊆ C \ q) (hVW : V ∩ W = {a,b})
    (hCD : C ∩ D = W) (hCM : C ⊆ M) (hDM : D ⊆ M)
    (hCF : C ∩ F = q) (hDF : D ∩ F = V)
    (γ : E → Y)
    (hne : ¬ ∃ f : C(C,Y), ∀ x : C, (x : E) ∈ q → f x = γ x) :
    ∃ A U : Set E, IsFinitePLBallPair ℝ U {a,b} ∧
      IsFinitePLBallPair (ℝ × ℝ) A (U ∪ W) ∧ A ⊆ C ∧ A ∩ q = U ∧
      IsFinitePLBallPair (ℝ × ℝ) (A ∪ D) (U ∪ V) ∧
      A ∪ D ⊆ M ∧ (A ∪ D) ∩ F = U ∪ V ∧ A ∩ D = W ∧
      ¬ ∃ f : C(↥(A ∪ D),Y), ∀ x : ↥(A ∪ D), (x : E) ∈ U ∪ V → f x = γ x := by
  obtain ⟨A,U,hU,hA,hcover,hinter,hUq,_,hAq,hnew,hnewM,hnewF,_⟩ :=
    exists_outermost_disk_surgery hC hD hW hV ha hb hab hproper hVW hCD hCM hDM hCF hDF
  have hAC (i : Bool) : A i ⊆ C := by
    cases i
    · exact subset_union_left.trans hcover.subset
    · exact subset_union_right.trans hcover.subset
  have hUW (i : Bool) : U i ∩ W = {a,b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact (hproper ⟨hx.2,hn⟩).2 ((hAq i).symm.subset hx.1).2
    · exact fun x hx => ⟨(hU i).1 hx,hW.1 hx⟩
  have hUV (i : Bool) : U i ∩ V = {a,b} := by
    apply Subset.antisymm
    · intro x hx
      have hxW : x ∈ W := hCD.subset
        ⟨hAC i ((hAq i).symm.subset hx.1).1,hD.1 (Or.inl hx.2)⟩
      exact hVW.subset ⟨hx.2,hxW⟩
    · exact fun x hx => ⟨(hU i).1 hx,hV.1 hx⟩
  obtain ⟨i,hi⟩ := exists_nonextendable_surgery_branch A U hC hU hA hcover hinter hUq
    hAq hnew hW hV hUW hUV γ (by
      rintro ⟨f,hf⟩
      exact hne ⟨f,fun x hx => hf x hx⟩)
  refine ⟨A i,U i,hU i,hA i,hAC i,hAq i,hnew i,hnewM i,hnewF i,?_,?_⟩
  · apply Subset.antisymm
    · exact fun x hx => hCD.subset ⟨hAC i hx.1,hx.2⟩
    · exact fun x hx => ⟨(hA i).1 (Or.inr hx),hD.1 (Or.inr hx)⟩
  · rintro ⟨f,hf⟩
    exact hi ⟨f,fun x hx => hf ⟨x,(hnew i).1 hx⟩ hx⟩

end PoincareMT.M76

