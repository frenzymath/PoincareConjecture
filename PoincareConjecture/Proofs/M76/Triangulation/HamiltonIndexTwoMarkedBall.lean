import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoRegionBalls










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76




structure HamiltonIndexTwoFrame (ι : Type*) [Fintype ι] where
  lower : ι → ℝ
  upper : ι → ℝ
  side : Set (ι → ℝ)
  outer : Bool → Set (ι → ℝ)
  rim : Bool → Set (ι → ℝ)
  boxBall : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (Icc lower upper)
    (frontier (Icc lower upper))
  outerBall : ∀ j, IsFinitePLBallPair (ℝ × ℝ) (outer j) (rim j)
  outerDisjoint : Disjoint (outer false) (outer true)
  frontier_eq : frontier (Icc lower upper) = (side ∪ outer false) ∪ outer true
  topRimNonempty : (rim true).Nonempty
  sidePL : FinitePiecewiseAffineOn (id : (ι → ℝ) → (ι → ℝ)) side





structure HamiltonIndexTwoMarkedBall {ι : Type*} [Fintype ι]
    (F : HamiltonIndexTwoFrame ι) where
  carrier : Set (ι → ℝ)
  disk : Bool → Set (ι → ℝ)
  ball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) carrier
    ((F.side ∪ disk false) ∪ disk true)
  subset_box : carrier ⊆ Icc F.lower F.upper
  diskBall : ∀ j, IsFinitePLBallPair (ℝ × ℝ) (disk j) (F.rim j)
  disk_outer : ∀ j, disk j ∩ F.outer j = F.rim j
  disk_side : ∀ j, disk j ∩ F.side = F.rim j
  disksDisjoint : Disjoint (disk false) (disk true)
  boundary_outer : ∀ j, ((F.side ∪ disk false) ∪ disk true) ∩ F.outer j = F.rim j

section Boundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_fixed_patch_disk_union {s t p q : Set E}
    (hp : FinitePiecewiseAffineOn (id : E → E) p)
    (hs : s ∩ p = q) (ht : t ∩ p = q)
    (e : s ≃ₜ t) (he : e.IsFinitePL)
    (hfix : ∀ x : s, (x : E) ∈ q → (e x : E) = x) :
    ∃ H : (p ∪ s : Set E) ≃ₜ (p ∪ t : Set E), H.IsFinitePL ∧
      (∀ x : p, (H ⟨x, Or.inl x.property⟩ : E) = x) ∧
      ∀ x : s, (H ⟨x, Or.inr x.property⟩ : E) = e x := by
  have hid : (Homeomorph.refl p).IsFinitePL := ⟨id, hp, fun _ => rfl⟩
  have hoverlap (x : p) : (x : E) ∈ s ↔ (Homeomorph.refl p x : E) ∈ t := by
    change (x : E) ∈ s ↔ (x : E) ∈ t
    exact ⟨fun hx => (ht.symm.subset (hs.subset ⟨hx, x.property⟩)).1,
      fun hx => (hs.symm.subset (ht.subset ⟨hx, x.property⟩)).1⟩
  have hagree (x : E) (hxp : x ∈ p) (hxs : x ∈ s) :
      (Homeomorph.refl p ⟨x, hxp⟩ : E) = e ⟨x, hxs⟩ :=
    (hfix ⟨x, hxs⟩ (hs.subset ⟨hxs, hxp⟩)).symm
  obtain ⟨H, hH, hHp, hHs⟩ := Homeomorph.exists_union_finitePL
    (Homeomorph.refl p) e hid he hoverlap hagree
  exact ⟨H, hH, hHp, hHs⟩

end Boundary





theorem exists_hamilton_indexTwo_boundary_map
    {ι : Type*} [Fintype ι] (F : HamiltonIndexTwoFrame ι)
    (S T : HamiltonIndexTwoMarkedBall F)
    (e : ∀ j, S.disk j ≃ₜ T.disk j) (he : ∀ j, (e j).IsFinitePL)
    (hfix : ∀ j (x : S.disk j), (x : ι → ℝ) ∈ F.rim j → (e j x : ι → ℝ) = x) :
    ∃ H : ((F.side ∪ S.disk false) ∪ S.disk true : Set (ι → ℝ)) ≃ₜ
        ((F.side ∪ T.disk false) ∪ T.disk true : Set (ι → ℝ)),
      H.IsFinitePL ∧
      (∀ x : F.side, (H ⟨x, Or.inl (Or.inl x.property)⟩ : ι → ℝ) = x) ∧
      (∀ x : S.disk false, (H ⟨x, Or.inl (Or.inr x.property)⟩ : ι → ℝ) = e false x) ∧
      ∀ x : S.disk true, (H ⟨x, Or.inr x.property⟩ : ι → ℝ) = e true x := by
  obtain ⟨f, hf, hfside, hfdisk⟩ := exists_fixed_patch_disk_union F.sidePL
    (S.disk_side false) (T.disk_side false) (e false) (he false) (hfix false)
  have hside (R : HamiltonIndexTwoMarkedBall F) (j : Bool) : F.rim j ⊆ F.side :=
    fun _ hx => ((R.disk_side j).symm.subset hx).2
  have hinter (R : HamiltonIndexTwoMarkedBall F) :
      (F.side ∪ R.disk false) ∩ R.disk true = F.rim true := by
    ext x
    constructor
    · rintro ⟨hx | hx, hy⟩
      · exact (R.disk_side true).subset ⟨hy, hx⟩
      · exact (Set.disjoint_left.mp R.disksDisjoint hx hy).elim
    · intro hx
      exact ⟨Or.inl (hside R true hx), (R.diskBall true).1 hx⟩
  have hmem := f.mem_subset_iff_of_extension (Homeomorph.refl (F.rim true))
    (fun _ hx => Or.inl (hside S true hx))
    (fun _ hx => Or.inl (hside T true hx))
    (fun x => Subtype.ext (hfside ⟨x, hside S true x.property⟩))
  have hoverlap (x : (F.side ∪ S.disk false : Set (ι → ℝ))) :
      (x : ι → ℝ) ∈ S.disk true ↔ (f x : ι → ℝ) ∈ T.disk true := by
    have hx : (x : ι → ℝ) ∈ S.disk true ↔ (x : ι → ℝ) ∈ F.rim true := by
      rw [← hinter S]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (f x : ι → ℝ) ∈ F.rim true ↔ (f x : ι → ℝ) ∈ T.disk true := by
      rw [← hinter T]
      simp only [mem_inter_iff, (f x).property, true_and]
    exact hx.trans ((hmem x).trans hy)
  have hagree (x : ι → ℝ) (hxf : x ∈ F.side ∪ S.disk false)
      (hxe : x ∈ S.disk true) : (f ⟨x, hxf⟩ : ι → ℝ) = e true ⟨x, hxe⟩ := by
    have hxq : x ∈ F.rim true := (hinter S).subset ⟨hxf, hxe⟩
    exact (hfside ⟨x, hside S true hxq⟩).trans (hfix true ⟨x, hxe⟩ hxq).symm
  obtain ⟨H, hH, hHf, hHe⟩ := Homeomorph.exists_union_finitePL f (e true) hf (he true)
    hoverlap hagree
  refine ⟨H, hH, ?_, ?_, hHe⟩
  · intro x
    exact (hHf ⟨x, Or.inl x.property⟩).trans (hfside x)
  · intro x
    exact (hHf ⟨x, Or.inr x.property⟩).trans (hfdisk x)

end PoincareConjecture.M76
