import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductRescaling

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem image_positive_time_scaling {A : Type*} (S : Set A)
    {d : ℝ} (hd : 0 < d) (v : ℝ) :
    (fun z : A × ℝ => (z.1,d*z.2)) '' (S ×ˢ Ioo (-v) v) =
      S ×ˢ Ioo (-(d*v)) (d*v) := by
  apply Subset.antisymm
  · rintro _ ⟨z,⟨hz,ht⟩,rfl⟩
    exact ⟨hz,by nlinarith [mul_lt_mul_of_pos_left ht.1 hd],
      mul_lt_mul_of_pos_left ht.2 hd⟩
  · rintro ⟨z,t⟩ ⟨hz,ht⟩
    refine ⟨(z,t/d),⟨hz,?_,?_⟩,?_⟩
    · exact (lt_div_iff₀ hd).mpr (by nlinarith [ht.1])
    · exact (div_lt_iff₀ hd).mpr (by nlinarith [ht.2])
    · exact Prod.ext rfl (mul_div_cancel₀ _ hd.ne')

theorem rescaled_open_image {X A : Type*} {f g : A × ℝ → X}
    {d : ℝ} (hd : 0 < d) (hmap : ∀ z, g z = f (z.1,d*z.2))
    (S : Set A) (v : ℝ) :
    g '' (S ×ˢ Ioo (-v) v) = f '' (S ×ˢ Ioo (-(d*v)) (d*v)) := by
  rw [show g = f ∘ (fun z => (z.1,d*z.2)) from funext hmap,
    image_comp,image_positive_time_scaling S hd v]

theorem exists_narrower_original_marked_disk_product
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (F : V2 × ℝ → X)
    {a d : ℝ} (ha : 0 < a) (hd : 0 < d) (hda : d ≤ a)
    (hPU : MapsTo P.map (Disk ×ˢ I) U)
    (hmark : ∀ z ∈ Rim, ∀ t ∈ I, P.map (z,t) = F (z,a*t))
    (hopen : ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-v) v))) ∧
      IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Rim ×ˢ Ioo (-v) v)))) :
    ∃ Q : OriginalDiskProduct e R j,
      (∀ z, Q.map z = P.map (z.1,(d/a)*z.2)) ∧
      MapsTo Q.map (Disk ×ˢ I) U ∧
      Q.map '' (Disk ×ˢ I) ⊆ P.map '' (Disk ×ˢ I) ∧
      (∀ z ∈ Rim, ∀ t ∈ I, Q.map (z,t) = F (z,d*t)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (Q.map '' (Disk ×ˢ Ioo (-v) v))) ∧
        IsOpen ((Subtype.val : frontier R → X) ⁻¹' (Q.map '' (Rim ×ˢ Ioo (-v) v))) := by
  have hq : 0 < d/a := div_pos hd ha
  have hq1 : d/a ≤ 1 := (div_le_one ha).mpr hda
  have htime (t : ℝ) (ht : t ∈ I) : (d/a)*t ∈ I := by
    constructor <;> nlinarith [ht.1,ht.2]
  obtain ⟨Q,hQ⟩ := P.exists_rescaled_product hq hq1
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro z hz
    rw [hQ z]
    exact hPU ⟨hz.1,htime z.2 hz.2⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨(z.1,(d/a)*z.2),⟨hz.1,htime z.2 hz.2⟩,(hQ z).symm⟩
  · intro z hz t ht
    rw [hQ (z,t),hmark z hz _ (htime t ht)]
    congr 2
    field_simp
  · intro v hv hv1
    have hqv : 0 < (d/a)*v := mul_pos hq hv
    have hqv1 : (d/a)*v ≤ 1 := by nlinarith
    obtain ⟨hR,hF⟩ := hopen _ hqv hqv1
    rw [rescaled_open_image hq hQ Disk v,rescaled_open_image hq hQ Rim v]
    exact ⟨hR,hF⟩

end PoincareConjecture.M76.Dehn.Annuli
