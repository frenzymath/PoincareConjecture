import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoMarkedBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLClosedExtension

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

private theorem finitePL_identity_of_ball
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s b : Set E} (h : IsFinitePLBallPair V s b) :
    FinitePiecewiseAffineOn (id : E → E) s := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := h
  exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩

private theorem exists_marked_cap_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S T d D o q : Set E}
    (hS : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) S (d ∪ o))
    (hT : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) T (D ∪ o))
    (ho : IsFinitePLBallPair (ℝ × ℝ) o q)
    (hdo : d ∩ o = q) (hDo : D ∩ o = q)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (hfix : ∀ x : d, (x : E) ∈ q → (e x : E) = x) :
    ∃ H : S ≃ₜ T, H.IsFinitePL ∧
      (∀ x : o, (H ⟨x, hS.1 (Or.inr x.property)⟩ : E) = x) ∧
      ∀ x : d, (H ⟨x, hS.1 (Or.inl x.property)⟩ : E) = e x := by
  obtain ⟨bnd, hbnd, hbndo, hbndd⟩ := exists_fixed_patch_disk_union
    (finitePL_identity_of_ball ho) hdo hDo e he hfix
  have hS' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) S (o ∪ d) := by
    rwa [union_comm o d]
  have hT' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) T (o ∪ D) := by
    rwa [union_comm o D]
  obtain ⟨H, hH, hHb, _⟩ := hS'.exists_extension hT' bnd hbnd
  refine ⟨H, hH, ?_, ?_⟩
  · intro x
    exact (congrArg (fun y : T => (y : E)) (hHb ⟨x, Or.inl x.property⟩)).trans (hbndo x)
  · intro x
    exact (congrArg (fun y : T => (y : E)) (hHb ⟨x, Or.inr x.property⟩)).trans (hbndd x)

private theorem glue_exact_disk_maps
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s u t v d D : Set E}
    (hsource : s ∩ u = d) (htarget : t ∩ v = D)
    (f : s ≃ₜ t) (g : u ≃ₜ v) (e : d ≃ₜ D)
    (hf : f.IsFinitePL) (hg : g.IsFinitePL)
    (hfd : ∀ x : d, (f ⟨x, (hsource.symm.subset x.property).1⟩ : E) = e x)
    (hgd : ∀ x : d, (g ⟨x, (hsource.symm.subset x.property).2⟩ : E) = e x) :
    ∃ H : (s ∪ u : Set E) ≃ₜ (t ∪ v : Set E), H.IsFinitePL ∧
      (∀ x : s, (H ⟨x, Or.inl x.property⟩ : E) = f x) ∧
      ∀ x : u, (H ⟨x, Or.inr x.property⟩ : E) = g x := by
  have hmem := f.mem_subset_iff_of_extension e
    (fun _ hx => (hsource.symm.subset hx).1)
    (fun _ hx => (htarget.symm.subset hx).1) (fun x => Subtype.ext (hfd x))
  have hoverlap (x : s) : (x : E) ∈ u ↔ (f x : E) ∈ v := by
    have hx : (x : E) ∈ u ↔ (x : E) ∈ d := by
      rw [← hsource]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (f x : E) ∈ D ↔ (f x : E) ∈ v := by
      rw [← htarget]
      simp only [mem_inter_iff, (f x).property, true_and]
    exact hx.trans ((hmem x).trans hy)
  have hagree (x : E) (hxs : x ∈ s) (hxu : x ∈ u) :
      (f ⟨x, hxs⟩ : E) = g ⟨x, hxu⟩ := by
    have hxd : x ∈ d := hsource.subset ⟨hxs, hxu⟩
    exact (hfd ⟨x, hxd⟩).trans (hgd ⟨x, hxd⟩).symm
  exact Homeomorph.exists_union_finitePL f g hf hg hoverlap hagree

private theorem marked_cap_regions
    {ι : Type*} [Fintype ι] (hdim : Fintype.card ι = 3)
    (F : HamiltonIndexTwoFrame ι) (R : HamiltonIndexTwoMarkedBall F) :
    ∃ C : Bool → Set (ι → ℝ),
      (∀ j, IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (C j) (R.disk j ∪ F.outer j)) ∧
      (∀ j, C j ⊆ Icc F.lower F.upper) ∧
      R.carrier ∩ C false = R.disk false ∧
      (R.carrier ∪ C false) ∩ C true = R.disk true ∧
      (R.carrier ∪ C false) ∪ C true = Icc F.lower F.upper := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hC₀L, hC₁L, hcontact₀, hcontact₁, hcover⟩ :=
    exists_hamilton_indexTwo_cap_regions hdim F.boxBall R.ball R.subset_box
      (R.diskBall false) (R.diskBall true) (F.outerBall false) (F.outerBall true)
      (R.disk_outer false) (R.disk_outer true) (R.disk_side false) (R.disk_side true)
      R.disksDisjoint F.outerDisjoint (R.boundary_outer false) (R.boundary_outer true)
      F.frontier_eq F.topRimNonempty
  let C : Bool → Set (ι → ℝ) := fun j => if j then C₁ else C₀
  refine ⟨C, ?_, ?_, hcontact₀, hcontact₁, hcover⟩
  · intro j
    cases j <;> assumption
  · intro j
    cases j <;> assumption

theorem exists_hamilton_indexTwo_relative_placement
    {ι : Type*} [Fintype ι] (hdim : Fintype.card ι = 3)
    (F : HamiltonIndexTwoFrame ι) (S T : HamiltonIndexTwoMarkedBall F)
    (e : ∀ j, S.disk j ≃ₜ T.disk j) (he : ∀ j, (e j).IsFinitePL)
    (hfix : ∀ j (x : S.disk j), (x : ι → ℝ) ∈ F.rim j → (e j x : ι → ℝ) = x) :
    ∃ Q : (ι → ℝ) ≃ₜ (ι → ℝ),
      FinitePiecewiseAffineOn (Q : (ι → ℝ) → (ι → ℝ)) (Icc F.lower F.upper) ∧
      Q '' S.carrier = T.carrier ∧
      EqOn Q id (interior (Icc F.lower F.upper))ᶜ := by
  obtain ⟨CS, hCS, _, hCS₀, hCS₁, hcoverS⟩ := marked_cap_regions hdim F S
  obtain ⟨CT, hCT, _, hCT₀, hCT₁, hcoverT⟩ := marked_cap_regions hdim F T
  have hsd (R : HamiltonIndexTwoMarkedBall F) (j : Bool) : R.disk j ⊆ R.carrier := by
    intro x hx
    cases j with
    | false => exact R.ball.1 (Or.inl (Or.inr hx))
    | true => exact R.ball.1 (Or.inr hx)
  have hss (R : HamiltonIndexTwoMarkedBall F) : F.side ⊆ R.carrier :=
    fun _ hx => R.ball.1 (Or.inl (Or.inl hx))
  obtain ⟨bnd, hbnd, hbndSide, hbnd₀, hbnd₁⟩ :=
    exists_hamilton_indexTwo_boundary_map F S T e he hfix
  obtain ⟨M, hM, hMbnd, _⟩ := S.ball.exists_extension T.ball bnd hbnd
  have hMside (x : F.side) : (M ⟨x, hss S x.property⟩ : ι → ℝ) = x :=
    (congrArg (fun y : T.carrier => (y : ι → ℝ))
      (hMbnd ⟨x, Or.inl (Or.inl x.property)⟩)).trans (hbndSide x)
  have hMd (j : Bool) (x : S.disk j) :
      (M ⟨x, hsd S j x.property⟩ : ι → ℝ) = e j x := by
    cases j with
    | false =>
        exact (congrArg (fun y : T.carrier => (y : ι → ℝ))
          (hMbnd ⟨x, Or.inl (Or.inr x.property)⟩)).trans (hbnd₀ x)
    | true =>
        exact (congrArg (fun y : T.carrier => (y : ι → ℝ))
          (hMbnd ⟨x, Or.inr x.property⟩)).trans (hbnd₁ x)
  have hcap (j : Bool) : ∃ N : CS j ≃ₜ CT j, N.IsFinitePL ∧
      (∀ x : F.outer j, (N ⟨x, (hCS j).1 (Or.inr x.property)⟩ : ι → ℝ) = x) ∧
      ∀ x : S.disk j, (N ⟨x, (hCS j).1 (Or.inl x.property)⟩ : ι → ℝ) = e j x :=
    exists_marked_cap_extension (hCS j) (hCT j) (F.outerBall j)
      (S.disk_outer j) (T.disk_outer j) (e j) (he j) (hfix j)
  choose N hN hNouter hNd using hcap
  obtain ⟨H₀, hH₀, hH₀M, hH₀N⟩ := glue_exact_disk_maps hCS₀ hCT₀
    M (N false) (e false) hM (hN false) (hMd false) (hNd false)
  have hH₀d (x : S.disk true) :
      (H₀ ⟨x, (hCS₁.symm.subset x.property).1⟩ : ι → ℝ) = e true x :=
    (hH₀M ⟨x, hsd S true x.property⟩).trans (hMd true x)
  obtain ⟨H₁, hH₁, hH₁H₀, hH₁N⟩ := glue_exact_disk_maps hCS₁ hCT₁
    H₀ (N true) (e true) hH₀ (hN true) hH₀d (hNd true)
  let H : (Icc F.lower F.upper) ≃ₜ (Icc F.lower F.upper) :=
    (Homeomorph.setCongr hcoverS.symm).trans (H₁.trans (Homeomorph.setCongr hcoverT))
  have hH : H.IsFinitePL := hH₁.setCongr hcoverS hcoverT
  have hHmid (x : S.carrier) :
      (H ⟨x, S.subset_box x.property⟩ : ι → ℝ) = M x :=
    (hH₁H₀ ⟨x, Or.inl x.property⟩).trans (hH₀M x)
  have hHfix (x : Icc F.lower F.upper)
      (hx : (x : ι → ℝ) ∈ frontier (Icc F.lower F.upper)) : H x = x := by
    apply Subtype.ext
    rcases F.frontier_eq.subset hx with (hside | houter) | houter
    · exact (hHmid ⟨x, hss S hside⟩).trans (hMside ⟨x, hside⟩)
    · exact (hH₁H₀ ⟨x, Or.inr ((hCS false).1 (Or.inr houter))⟩).trans
        ((hH₀N ⟨x, (hCS false).1 (Or.inr houter)⟩).trans (hNouter false ⟨x, houter⟩))
    · exact (hH₁N ⟨x, (hCS true).1 (Or.inr houter)⟩).trans (hNouter true ⟨x, houter⟩)
  let Q := H.closedExtension isClosed_Icc hHfix
  have hQmid (x : S.carrier) : Q x = (M x : ι → ℝ) :=
    (H.closedExtension_apply_mem isClosed_Icc hHfix (S.subset_box x.property)).trans (hHmid x)
  refine ⟨Q, ?_, ?_, ?_⟩
  · obtain ⟨f, hf, hHf⟩ := hH
    exact hf.congr fun x hx => (hHf ⟨x, hx⟩).symm.trans
      (H.closedExtension_apply_mem isClosed_Icc hHfix hx).symm
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [hQmid ⟨x, hx⟩]
      exact (M ⟨x, hx⟩).property
    · intro y hy
      let x := M.symm ⟨y, hy⟩
      refine ⟨x, x.property, ?_⟩
      rw [hQmid x]
      exact congrArg Subtype.val (M.apply_symm_apply ⟨y, hy⟩)
  · intro x hx
    exact H.closedExtension_apply_notMem_interior isClosed_Icc hHfix hx

end PoincareConjecture.M76
