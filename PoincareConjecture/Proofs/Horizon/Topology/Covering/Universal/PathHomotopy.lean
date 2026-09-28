




module

public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected


import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps


























public section

open scoped unitInterval
open Topology Set

namespace Path
variable {X : Type*} [TopologicalSpace X]




def codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    Path x y where
  toFun := s.codRestrict γ hmem
  continuous_toFun := γ.continuous.codRestrict hmem
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target


@[simp]
theorem codRestrict_coe {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) (t : I) :
    (γ.codRestrict hmem t : X) = γ t := by
  rfl


@[simp]
theorem map_codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    (γ.codRestrict hmem).map continuous_subtype_val = γ := by
  ext t
  simp


@[simp]
theorem map_refl {Y : Type*} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (a : X) :
    (Path.refl a).map hf = Path.refl (f a) :=
  rfl



theorem truncateOfLE_range_subset {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) {U : Set X} (hU : Set.Icc t₀ t₁ ⊆ γ.extend ⁻¹' U) :
    Set.range (γ.truncateOfLE h) ⊆ U := by
  rintro _ ⟨s, rfl⟩
  dsimp [truncateOfLE, truncate]
  apply hU
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _






noncomputable def initialSegmentFamily {a b : X} (γ : Path a b) (t : I) :
    Path a (γ t) :=
  (γ.truncate 0 t).cast (by rw [min_eq_left t.2.1, γ.extend_zero]) (γ.extend_apply t.2).symm


theorem mem_pathComponent {a b : X} (γ : Path a b) (t : I) : γ t ∈ pathComponent a :=
  ⟨γ.initialSegmentFamily t⟩


theorem mem_pathComponent_of_mem {a b x₀ : X} (γ : Path a b) (ha : a ∈ pathComponent x₀)
    (t : I) : γ t ∈ pathComponent x₀ :=
  Joined.mem_pathComponent (γ.mem_pathComponent t) ha

theorem continuous_initialSegmentFamily_uncurry {a b : X} (γ : Path a b) :
    Continuous ↿(initialSegmentFamily γ) := by
  have hincl : Continuous (fun ts : I × I ↦ ((ts.1 : ℝ), ts.2) : I × I → ℝ × I) := by fun_prop
  have htrunc : Continuous (fun ts : I × I ↦ γ.truncate 0 ts.1 ts.2 : I × I → X) :=
    (γ.truncate_const_continuous_family 0).comp hincl
  simpa [initialSegmentFamily] using! htrunc

@[simp] private theorem initialSegmentFamily_apply {a b : X} (γ : Path a b) (t s : I) :
    initialSegmentFamily γ t s = γ.extend (min (s : ℝ) t) := by
  simp [initialSegmentFamily, Path.truncate, max_eq_left s.2.1]

@[simp] theorem initialSegmentFamily_zero {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 0 = (Path.refl a).cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, γ.extend_zero, Path.refl, min_eq_right s.2.1]


  rfl

@[simp] theorem initialSegmentFamily_one {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 1 = γ.cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, min_eq_left s.2.2, γ.extend_apply s.2]








theorem exists_homotopy_forall_mem_of_isSimplyConnected {V : Set X} (hV : IsSimplyConnected V)
    {a b : X} {p q : Path a b} (hp : ∀ t, p t ∈ V) (hq : ∀ t, q t ∈ V) :
    ∃ K : p.Homotopy q, ∀ t x, K (t, x) ∈ V := by
  have := hV.simplyConnectedSpace
  have haV : a ∈ V := p.source ▸ hp 0
  have hbV : b ∈ V := p.target ▸ hp 1
  obtain ⟨h⟩ := SimplyConnectedSpace.paths_homotopic
    (Path.codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) p hp)
    (Path.codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) q hq)

  refine ⟨(h.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))).cast
    (Path.map_codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) p hp)
    (Path.map_codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) q hq), fun t x => ?_⟩
  simp




theorem homotopic_of_continuous_square {a b : X} {p q : Path a b} (K : I × I → X)
    (hK_cont : Continuous K) (hK_zero : ∀ s, K (0, s) = p s) (hK_one : ∀ s, K (1, s) = q s)
    (hK_left : ∀ t, K (t, 0) = a) (hK_right : ∀ t, K (t, 1) = b) : p.Homotopic q :=
  ⟨{ toFun := K
     continuous_toFun := hK_cont
     map_zero_left := hK_zero
     map_one_left := hK_one
     prop' := by
       intro t s hs
       rcases hs with rfl | hs
       · exact (hK_left t).trans p.source.symm
       · rw [Set.mem_singleton_iff] at hs
         subst hs
         exact (hK_right t).trans p.target.symm }⟩

end Path

namespace Path
variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Homotopic.Quotient




instance instTopologicalSpace (x₀ x : X) :
    TopologicalSpace (Path.Homotopic.Quotient x₀ x) :=
  inferInstanceAs (TopologicalSpace (Quotient _))



theorem isOpen_iff_preimage_mk {x₀ x₁ : X} {S : Set (Path.Homotopic.Quotient x₀ x₁)} :
    IsOpen S ↔ IsOpen ((Path.Homotopic.Quotient.mk : Path x₀ x₁ →
      Path.Homotopic.Quotient x₀ x₁) ⁻¹' S) :=


  Iff.rfl



@[simp]
theorem subpath_trans {x y : X} (p : Path x y) (a b c : unitInterval) :
    trans (mk (p.subpath a b)) (mk (p.subpath b c)) =
      mk (p.subpath a c) := by
  simp only [← mk_trans, eq]
  exact ⟨Path.Homotopy.subpathTransSubpath p a b c⟩


theorem subpath_self {x y : X} (p : Path x y) (a : unitInterval) :
    mk (p.subpath a a) = refl (p a) := by
  simp only [← mk_refl, eq]
  rw [Path.subpath_self]



theorem subpath_zero_one {x y : X} (p : Path x y) :
    mk (p.subpath 0 1) = (mk p).cast (by simp) (by simp) := by
  simp only [← mk_cast, eq]
  rw [Path.subpath_zero_one]

end Homotopic.Quotient

end Path

namespace Path.Homotopic
variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}


theorem trans_left_of_nullhomotopic {γ₀ : Path x₀ x₀} {γ₁ : Path x₀ x₁}
    (hγ₀ : γ₀.Homotopic (Path.refl x₀)) : (γ₀.trans γ₁).Homotopic γ₁ :=
  (hcomp hγ₀ (.refl γ₁)).trans (refl_trans γ₁)


theorem trans_right_of_nullhomotopic {γ₀ : Path x₀ x₁} {γ₁ : Path x₁ x₁}
    (hγ₁ : γ₁.Homotopic (Path.refl x₁)) : (γ₀.trans γ₁).Homotopic γ₀ :=
  (hcomp (.refl γ₀) hγ₁).trans (trans_refl γ₀)



theorem of_trans_symm {γ γ' : Path x₀ x₁}
    (h : (γ.trans γ'.symm).Homotopic (Path.refl x₀)) : γ.Homotopic γ' :=
  (trans_refl γ).symm |>.trans <|
  (hcomp (.refl γ) (symm_trans γ').symm) |>.trans <|
  (trans_assoc γ γ'.symm γ').symm |>.trans <|
  (hcomp h (.refl γ')) |>.trans <|
  refl_trans γ'



theorem trans_right_cancel {x₀ x₁ x₂ : X} {γ δ : Path x₀ x₁} {e : Path x₁ x₂}
    (h : (γ.trans e).Homotopic (δ.trans e)) : γ.Homotopic δ := by
  have hγ : ((γ.trans e).trans e.symm).Homotopic γ :=
    (trans_assoc γ e e.symm).trans (trans_right_of_nullhomotopic (trans_symm e))
  have hδ : ((δ.trans e).trans e.symm).Homotopic δ :=
    (trans_assoc δ e e.symm).trans (trans_right_of_nullhomotopic (trans_symm e))
  exact hγ.symm.trans ((h.hcomp (refl e.symm)).trans hδ)



theorem trans_left_cancel {x₀ x₁ x₂ : X} {e : Path x₀ x₁} {γ δ : Path x₁ x₂}
    (h : (e.trans γ).Homotopic (e.trans δ)) : γ.Homotopic δ := by
  have hγ : (e.symm.trans (e.trans γ)).Homotopic γ :=
    (trans_assoc e.symm e γ).symm.trans (trans_left_of_nullhomotopic (symm_trans e))
  have hδ : (e.symm.trans (e.trans δ)).Homotopic δ :=
    (trans_assoc e.symm e δ).symm.trans (trans_left_of_nullhomotopic (symm_trans e))
  exact hγ.symm.trans (((refl e.symm).hcomp h).trans hδ)



theorem map_nullhomotopic_of_nullhomotopic {Y : Type*} [TopologicalSpace Y] {f : C(X, Y)}
    (hf : f.Nullhomotopic) {a : X} (γ : Path a a) :
    (γ.map (map_continuous f)).Homotopic (Path.refl (f a)) := by
  obtain ⟨c, ⟨F⟩⟩ := hf
  have key := Path.Homotopic.map_trans_evalAt F γ
  have hconst : γ.map (map_continuous (ContinuousMap.const X c)) = Path.refl c := by ext t; rfl
  rw [hconst] at key
  exact Path.Homotopic.trans_right_cancel
    ((key.trans (Path.Homotopic.trans_refl _)).trans (Path.Homotopic.refl_trans _).symm)



theorem refl_of_forall_mem_of_nullhomotopic {s : Set X}
    (hs : (ContinuousMap.mk (Subtype.val : s → X) continuous_subtype_val).Nullhomotopic)
    {x : X} (γ : Path x x) (hγ : ∀ t, γ t ∈ s) : γ.Homotopic (Path.refl x) := by
  have hx : x ∈ s := γ.source ▸ hγ 0
  have hmap := map_nullhomotopic_of_nullhomotopic hs
    (γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨x, hx⟩) hγ)
  rwa [Path.map_codRestrict] at hmap

namespace Quotient
variable {x₀ x₁ : X}


@[simp, grind =]
theorem refl_cast {x y : X} (h : y = x) : (refl x).cast h h = refl y := by


  cases h; rfl



theorem eq_of_trans_symm {γ γ' : Homotopic.Quotient x₀ x₁}
    (h : trans γ (symm γ') = refl x₀) : γ = γ' := by
  induction γ using Quotient.ind with | mk γ =>
  induction γ' using Quotient.ind with | mk γ' =>
  simp only [← mk_trans, ← mk_symm, ← mk_refl] at h
  exact Quotient.sound (Homotopic.of_trans_symm (Quotient.exact h))

end Quotient
end Path.Homotopic
