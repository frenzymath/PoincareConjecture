import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.MarkedDoubleBallSphere
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary











set_option autoImplicit false

open Set Metric Geometry

namespace Geometry.SphereCylinder

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

abbrev cube : Set V3 := closedBall 0 1
abbrev rim : Set V3 := sphere 0 1
abbrev interval : Set ℝ := Icc 0 1
abbrev carrier : Set (V3 × ℝ) := rim ×ˢ interval
abbrev cap (b : Bool) : Set (V3 × ℝ) := cube ×ˢ {if b then 1 else 0}
abbrev capRim (b : Bool) : Set (V3 × ℝ) := rim ×ˢ {if b then 1 else 0}
abbrev box : Set (V3 × ℝ) := cube ×ˢ interval
abbrev boundary : Set (V3 × ℝ) := carrier ∪ (cube ×ˢ {0, 1})

private theorem cap_subset_boundary (b : Bool) : cap b ⊆ boundary := by
  intro x hx
  exact Or.inr ⟨hx.1, by cases b; exact Or.inl hx.2; exact Or.inr hx.2⟩

private theorem boundary_subset_box : boundary ⊆ box := by
  rintro x (hx | hx)
  · exact ⟨sphere_subset_closedBall hx.1, hx.2⟩
  · refine ⟨hx.1, ?_⟩
    rcases hx.2 with h | h <;> rw [h] <;> norm_num

private theorem boundary_sdiff_cap (b : Bool) :
    boundary \ (cap b \ capRim b) = carrier ∪ cap (!b) := by
  ext x
  cases b <;>
    simp only [boundary, carrier, cap, capRim, Bool.false_eq_true, ite_false, ite_true,
      Bool.not_false, Bool.not_true, mem_sdiff, mem_union, mem_prod, mem_insert_iff,
      mem_singleton_iff]
  all_goals
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact Or.inl hx
      · by_cases h : x.1 ∈ rim
        · exact Or.inl ⟨h, by rcases hx.2 with h | h <;> rw [h] <;> norm_num⟩
        · right
          rcases hx.2 with h0 | h1
          all_goals first | exact ⟨hx.1, ‹_›⟩ | exact (hn ⟨⟨hx.1, ‹_›⟩, fun hc => h hc.1⟩).elim
    · rintro (hx | hx)
      · exact ⟨Or.inl hx, fun h => h.2 ⟨hx.1, h.1.2⟩⟩
      · refine ⟨Or.inr ⟨hx.1, ?_⟩, ?_⟩
        · first | exact Or.inl hx.2 | exact Or.inr hx.2
        · intro h
          have := hx.2.symm.trans h.1.2
          norm_num at this



theorem exists_marked_punctured_sphere_model :
    ∃ (A r : Bool → Set V4)
      (H : carrier ≃ₜ (CubicalThreeSphere.sphere \ ⋃ b, A b \ r b : Set V4)),
      (∀ b, IsFinitePLBallPair V3 (A b) (r b)) ∧
      (∀ b, A b ⊆ CubicalThreeSphere.sphere) ∧
      Pairwise (fun b c => Disjoint (A b) (A c)) ∧
      (∀ b, IsOpen ((Subtype.val : CubicalThreeSphere.sphere → V4) ⁻¹' (A b \ r b))) ∧
      H.IsFinitePL ∧
      ∀ x : carrier, (x : V3 × ℝ).2 ∈ ({0, 1} : Set ℝ) ↔
        (H x : V4) ∈ ⋃ b, r b := by
  classical
  have hc : IsFinitePLBallPair V3 cube rim := isFinitePLBallPair_unit_cube
  have hi := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hb : IsFinitePLBallPair (V3 × ℝ) box boundary := hc.prod hi
  let l : (V3 × ℝ) ≃L[ℝ] V4 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨C, hC, hmark⟩ := hb.exists_cube_chart l
  obtain ⟨f, hf, hval⟩ := hC
  have hfi : InjOn f box := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (C.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have hbd : f '' boundary = CubicalThreeSphere.sphere := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [← hval ⟨x, boundary_subset_box hx⟩]
      exact (hmark _).mp hx
    · intro y hy
      let y' : closedBall (0 : V4) 1 := ⟨y, isClosed_closedBall.frontier_subset hy⟩
      refine ⟨C.symm y', (hmark _).mpr ?_, ?_⟩
      · simpa using hy
      · rw [← hval, C.apply_symm_apply]
  let A : Bool → Set V4 := fun b => f '' cap b
  let r : Bool → Set V4 := fun b => f '' capRim b
  have hcap (b : Bool) : cap b ⊆ box := (cap_subset_boundary b).trans boundary_subset_box
  have hrim (b : Bool) : capRim b ⊆ cap b := prod_mono sphere_subset_closedBall subset_rfl
  have hA (b : Bool) : IsFinitePLBallPair V3 (A b) (r b) :=
    (hc.prod_singleton (if b then (1 : ℝ) else 0)).image_of_subset hf (hcap b) hfi
  have hAS (b : Bool) : A b ⊆ CubicalThreeSphere.sphere := by
    rw [← hbd]
    exact image_mono (cap_subset_boundary b)
  have himage (s t : Set (V3 × ℝ)) (hs : s ⊆ box) (ht : t ⊆ box) :
      f '' (s \ t) = f '' s \ f '' t := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
      rintro ⟨z, hz, hzx⟩
      exact hx.2 (hfi (ht hz) (hs hx.1) hzx ▸ hz)
    · rintro y ⟨⟨x, hx, rfl⟩, hn⟩
      exact ⟨x, ⟨hx, fun ht => hn ⟨x, ht, rfl⟩⟩, rfl⟩
  have hcompl (b : Bool) :
      CubicalThreeSphere.sphere \ (A b \ r b) = f '' (carrier ∪ cap (!b)) := by
    rw [← boundary_sdiff_cap b, himage boundary (cap b \ capRim b)
      boundary_subset_box (sdiff_subset.trans (hcap b)), hbd,
      himage (cap b) (capRim b) (hcap b) ((hrim b).trans (hcap b))]
  have hdis : Pairwise (fun b c => Disjoint (A b) (A c)) := by
    intro b c hbc
    rw [disjoint_left]
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := hfi (hcap b hx) (hcap c hz) (hxy.trans hzy.symm)
    have ht := hx.2.symm.trans ((congrArg Prod.snd hxz).trans hz.2)
    cases b <;> cases c <;> simp_all
  have ho (b : Bool) :
      IsOpen ((Subtype.val : CubicalThreeSphere.sphere → V4) ⁻¹' (A b \ r b)) := by
    have hcompact : IsCompact (carrier ∪ cap (!b)) :=
      (isCompact_sphere (0 : V3) 1 |>.prod isCompact_Icc).union
        (isCompact_closedBall (0 : V3) 1 |>.prod isCompact_singleton)
    have hsub : carrier ∪ cap (!b) ⊆ box :=
      union_subset (prod_mono sphere_subset_closedBall subset_rfl) (hcap (!b))
    have hclosed := (hcompact.image_of_continuousOn (hf.continuousOn.mono hsub)).isClosed
    have heq : (Subtype.val : CubicalThreeSphere.sphere → V4) ⁻¹' (A b \ r b) =
        ((Subtype.val : CubicalThreeSphere.sphere → V4) ⁻¹' f '' (carrier ∪ cap (!b)))ᶜ := by
      ext y
      rw [← hcompl]
      simp only [mem_preimage, mem_compl_iff, mem_sdiff, y.property, true_and, not_not]
    rw [heq]
    exact (hclosed.preimage continuous_subtype_val).isOpen_compl
  have htarget : f '' carrier = CubicalThreeSphere.sphere \ ⋃ b, A b \ r b := by
    have hsrc : boundary \ ⋃ b, cap b \ capRim b = carrier := by
      have heq : (⋃ b, cap b \ capRim b) =
          (cap true \ capRim true) ∪ (cap false \ capRim false) := by
        ext x
        simp [Bool.exists_bool, or_comm]
      rw [heq, ← sdiff_sdiff, boundary_sdiff_cap]
      ext x
      simp only [carrier, cap, capRim, Bool.not_true, Bool.false_eq_true,
        ite_false, mem_sdiff, mem_union, mem_prod, mem_singleton_iff]
      constructor
      · rintro ⟨hx | hx, hn⟩
        · exact hx
        · exact ⟨by by_contra h; exact hn ⟨hx, fun hr => h hr.1⟩,
            by rw [hx.2]; norm_num⟩
      · exact fun hx => ⟨Or.inl hx, fun h => h.2 ⟨hx.1, h.1.2⟩⟩
    rw [← hsrc, himage boundary (⋃ b, cap b \ capRim b) boundary_subset_box
      (iUnion_subset fun b => sdiff_subset.trans (hcap b)), hbd, image_iUnion]
    congr 1
    apply iUnion_congr
    intro b
    exact himage (cap b) (capRim b) (hcap b) ((hrim b).trans (hcap b))
  obtain ⟨K, hK, hKs⟩ := PoincareConjecture.M76.exists_finite_unitCubeSphere (ι := Fin 3)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hi
  obtain ⟨L, hL, hLs, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  have hLc : L.space = carrier := by simpa [hKs, hJs] using hLs
  have hfc : FinitePiecewiseAffineOn f carrier := by
    rw [← hLc]
    exact hf.restrict L hL (hLc.subset.trans (prod_mono sphere_subset_closedBall subset_rfl))
  obtain ⟨D, hD, hDval⟩ := hfc.exists_homeomorph_image
    (hfi.mono (prod_mono sphere_subset_closedBall subset_rfl))
  let H := D.trans (Homeomorph.setCongr htarget)
  refine ⟨A, r, H, hA, hAS, hdis, ho, hD.setCongr rfl htarget, ?_⟩
  intro x
  change (x : V3 × ℝ).2 ∈ ({0, 1} : Set ℝ) ↔ (D x : V4) ∈ ⋃ b, r b
  rw [hDval]
  constructor
  · rintro (hx | hx)
    · exact mem_iUnion.mpr ⟨false, x, ⟨x.property.1, hx⟩, rfl⟩
    · exact mem_iUnion.mpr ⟨true, x, ⟨x.property.1, hx⟩, rfl⟩
  · intro hx
    obtain ⟨b, z, hz, hzx⟩ := mem_iUnion.mp hx
    have heq := hfi ((hrim b).trans (hcap b) hz)
      ⟨sphere_subset_closedBall x.property.1, x.property.2⟩ hzx
    have ht := (congrArg Prod.snd heq).symm.trans hz.2
    cases b
    · exact Or.inl ht
    · exact Or.inr ht

end Geometry.SphereCylinder
