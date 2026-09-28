import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedDiskProduct
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



noncomputable def diskTimeReflection : (V2 × ℝ) ≃L[ℝ] (V2 × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ V2).prodCongr
    (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)

private theorem reflection_full_product :
    diskTimeReflection.symm '' (D2 ×ˢ Icc (-1 : ℝ) 1) = D2 ×ˢ Icc (-1 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q.1 ∈ D2 ∧ -q.2 ∈ Icc (-1 : ℝ) 1
    exact ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
  · intro hp
    refine ⟨(p.1, -p.2), ⟨hp.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hp.2.1, hp.2.2]
    · change (p.1, - -p.2) = p
      simp only [neg_neg, Prod.eta]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {R D : Set E} {b : D2 ≃ₜ D}

namespace HamiltonUnmarkedDiskProduct



noncomputable def reflected (P : HamiltonUnmarkedDiskProduct R b) :
    HamiltonUnmarkedDiskProduct R b where
  map := P.map ∘ diskTimeReflection
  piecewiseAffine := by
    have h := P.piecewiseAffine.precomp_affineEquiv diskTimeReflection.toContinuousAffineEquiv
    change FinitePiecewiseAffineOn (P.map ∘ diskTimeReflection)
      (diskTimeReflection.symm '' (D2 ×ˢ Icc (-1 : ℝ) 1)) at h
    rwa [reflection_full_product] at h
  injective := by
    intro p hp q hq he
    apply diskTimeReflection.injective
    apply P.injective _ _ he
    · exact ⟨hp.1, by change -p.2 ∈ Icc (-1 : ℝ) 1; constructor <;> linarith [hp.2.1, hp.2.2]⟩
    · exact ⟨hq.1, by change -q.2 ∈ Icc (-1 : ℝ) 1; constructor <;> linarith [hq.2.1, hq.2.2]⟩
  inside := by
    intro p hp
    exact P.inside ⟨hp.1,
      by change -p.2 ∈ Icc (-1 : ℝ) 1; constructor <;> linarith [hp.2.1, hp.2.2]⟩
  proper := by
    intro p hp
    exact P.proper (diskTimeReflection p) ⟨hp.1,
      by change -p.2 ∈ Icc (-1 : ℝ) 1; constructor <;> linarith [hp.2.1, hp.2.2]⟩
  central := by
    intro x
    change P.map ((x : V2), -(0 : ℝ)) = b x
    rw [neg_zero]
    exact P.central x



theorem reflected_positive_image (P : HamiltonUnmarkedDiskProduct R b) :
    P.reflected.map '' (D2 ×ˢ Icc (0 : ℝ) 1) =
      P.map '' (D2 ×ˢ Icc (-1 : ℝ) 0) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(p.1, -p.2), ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨(p.1, -p.2), ⟨hp.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hp.2.1, hp.2.2]
    · change P.map (p.1, - -p.2) = P.map p
      simp only [neg_neg, Prod.eta]



theorem reflected_open_image (P : HamiltonUnmarkedDiskProduct R b) :
    P.reflected.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1) =
      P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(p.1, -p.2), ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨(p.1, -p.2), ⟨hp.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hp.2.1, hp.2.2]
    · change P.map (p.1, - -p.2) = P.map p
      simp only [neg_neg, Prod.eta]



theorem central_image (P : HamiltonUnmarkedDiskProduct R b) :
    P.map '' (D2 ×ˢ ({0} : Set ℝ)) = D := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have ht : p.2 = 0 := hp.2
    have he : p = (p.1, (0 : ℝ)) := Prod.ext rfl ht
    rw [he, P.central ⟨p.1, hp.1⟩]
    exact (b ⟨p.1, hp.1⟩).property
  · intro y hy
    let x := b.symm ⟨y, hy⟩
    refine ⟨((x : V2), 0), ⟨x.property, rfl⟩, ?_⟩
    rw [P.central]
    exact congrArg Subtype.val (b.apply_symm_apply ⟨y, hy⟩)



theorem half_images_inter (P : HamiltonUnmarkedDiskProduct R b) :
    (P.map '' (D2 ×ˢ Icc (0 : ℝ) 1)) ∩
      (P.map '' (D2 ×ˢ Icc (-1 : ℝ) 0)) = D := by
  have hp : D2 ×ˢ Icc (0 : ℝ) 1 ⊆ D2 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
  have hn : D2 ×ˢ Icc (-1 : ℝ) 0 ⊆ D2 ×ˢ Icc (-1 : ℝ) 1 := by
    intro p hp
    exact ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩
  rw [← P.injective.image_inter hp hn]
  have hset : (D2 ×ˢ Icc (0 : ℝ) 1) ∩ (D2 ×ˢ Icc (-1 : ℝ) 0) =
      D2 ×ˢ ({0} : Set ℝ) := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1.1, le_antisymm hp.2.2.2 hp.1.2.1⟩
    · rintro ⟨hp, ht⟩
      change p.2 = 0 at ht
      simp only [mem_inter_iff, mem_prod, mem_Icc, ht]
      exact ⟨⟨hp, by norm_num⟩, ⟨hp, by norm_num⟩⟩
  rw [hset, P.central_image]

variable [FiniteDimensional ℝ E]




theorem half_ballPair (P : HamiltonUnmarkedDiskProduct R b)
    {u v : ℝ} (huv : u < v) (hu : -1 ≤ u) (hv : v ≤ 1) :
    IsFinitePLBallPair (V2 × ℝ) (P.map '' (D2 ×ˢ Icc u v))
      (P.map '' ((Q2 ×ˢ Icc u v) ∪ (D2 ×ˢ {u, v}))) := by
  have hball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod (isFinitePLBallPair_Icc huv)
  exact hball.image_of_subset P.piecewiseAffine
    (fun p hp => ⟨hp.1, hu.trans hp.2.1, hp.2.2.trans hv⟩) P.injective

omit [FiniteDimensional ℝ E] in



theorem half_frontier_contact (P : HamiltonUnmarkedDiskProduct R b)
    {u v : ℝ} (hu : -1 ≤ u) (hv : v ≤ 1) :
    (P.map '' (D2 ×ˢ Icc u v)) ∩ frontier R ⊆
      P.map '' ((Q2 ×ˢ Icc u v) ∪ (D2 ×ˢ {u, v})) := by
  rintro y ⟨⟨p, hp, rfl⟩, hy⟩
  have hpc : p ∈ D2 ×ˢ Icc (-1 : ℝ) 1 := ⟨hp.1, hu.trans hp.2.1, hp.2.2.trans hv⟩
  exact ⟨p, Or.inl ⟨(P.proper p hpc).mp hy, hp.2⟩, rfl⟩

end HamiltonUnmarkedDiskProduct



theorem positive_source_half_ballPair {w : ℝ} (hw : 0 < w) :
    IsFinitePLBallPair (V2 × ℝ) (D2 ×ˢ Icc 0 w)
      ((D2 ×ˢ ({w} : Set ℝ)) ∪ ((D2 ×ˢ {0}) ∪ (Q2 ×ˢ Icc 0 w))) := by
  have h := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod (isFinitePLBallPair_Icc hw)
  have he : (Q2 ×ˢ Icc 0 w) ∪ (D2 ×ˢ ({0, w} : Set ℝ)) =
      (D2 ×ˢ ({w} : Set ℝ)) ∪ ((D2 ×ˢ {0}) ∪ (Q2 ×ˢ Icc 0 w)) := by
    ext p
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  rwa [he] at h

end PoincareConjecture.M76.HamiltonIndexOne
