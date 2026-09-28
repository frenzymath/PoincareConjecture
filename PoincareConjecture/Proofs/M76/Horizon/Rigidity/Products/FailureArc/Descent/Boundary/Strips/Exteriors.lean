import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.CenterDissection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MiddleStripDiskComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.ShellSquareCharts









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_spanning_strip_exterior_disks
    {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (c : Bool → P2 → P2)
    (hcPL : ∀ i, FinitePiecewiseAffineOn (c i) source)
    (hci : ∀ i, InjOn (c i) source)
    (hcin : ∀ i, MapsTo (c i) source (T \ interior S))
    (houter : ∀ i z, z ∈ source → (c i z ∈ frontier T ↔ z.1 = 0))
    (hinner : ∀ i z, z ∈ source → (c i z ∈ frontier S ↔ z.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source)) :
    ∃ (positive : Bool → Bool) (E : Fin 2 → Set P2),
      let sign := fun (j : Fin 2) (i : Bool) ↦ if j = 0 then positive i else !(positive i)
      let W := fun j i ↦ c i '' arm (farArmParameter (sign j i))
      (∀ j, IsFinitePLBallPair P2 (E j)
        (((E j ∩ (frontier T ∪ frontier S)) ∪ W j false) ∪ W j true)) ∧
      (∀ j, E j ⊆ T \ interior S) ∧ Disjoint (E 0) (E 1) ∧
      (c false '' source ∪ c true '' source) ∪ (E 0 ∪ E 1) = T \ interior S ∧
      (∀ j i, E j ∩ (c i '' source) = W j i) ∧
      ∀ j i, IsFinitePLBallPair ℝ (W j i)
        {c i (0, farArmParameter (sign j i)), c i (1, farArmParameter (sign j i))} := by
  classical
  obtain ⟨D, positive, hL, hR, _, _, _, _, hpos, hneg⟩ :=
    exists_spanning_strip_center_dissection hS hT hST c hcPL hci hcin houter hinner hdis
  let sign (j : Fin 2) (i : Bool) := if j = 0 then positive i else !(positive i)
  let H (j : Fin 2) (i : Bool) := c i '' halfSource (sign j i)
  let W (j : Fin 2) (i : Bool) := c i '' arm (farArmParameter (sign j i))
  let E (j : Fin 2) := D.disk j \ ((H j false \ W j false) ∪ (H j true \ W j true))
  let Q := frontier T ∪ frontier S
  have hQ (i : Bool) (z : P2) (hz : z ∈ source) :
      c i z ∈ Q ↔ z.1 = 0 ∨ z.1 = 1 := by
    change c i z ∈ frontier T ∪ frontier S ↔ _
    rw [mem_union, houter i z hz, hinner i z hz]
  have hhalf (j : Fin 2) (i : Bool) : H j i ⊆ D.disk j := by
    fin_cases j
    · exact hpos i
    · exact hneg i
  have hparts (j : Fin 2) : D.disk j ∩ Q = D.outer j ∪ D.inner j := by
    ext z
    constructor
    · rintro ⟨hz, hzo | hzi⟩
      · exact Or.inl ((D.outer_in_disk_iff j ⟨z, hz⟩).mp hzo)
      · exact Or.inr ((D.inner_in_disk_iff j ⟨z, hz⟩).mp hzi)
    · rintro (hzo | hzi)
      · have hz := D.outer_subset_disk j hzo
        exact ⟨hz, Or.inl ((D.outer_in_disk_iff j ⟨z, hz⟩).mpr hzo)⟩
      · have hz := D.inner_subset_disk j hzi
        exact ⟨hz, Or.inr ((D.inner_in_disk_iff j ⟨z, hz⟩).mpr hzi)⟩
  have hQM (j : Fin 2) :
      (D.outer j ∪ D.inner j) ∪ (D.left ∪ D.right) =
        ((D.disk j ∩ Q) ∪ c false '' arm 0) ∪ c true '' arm 0 := by
    rw [hparts, hL, hR]
    exact (union_assoc _ _ _).symm
  have hdata (j : Fin 2) :
      IsFinitePLBallPair P2 (E j) (((E j ∩ Q) ∪ W j false) ∪ W j true) ∧
      (H j false ∪ H j true) ∪ E j = D.disk j ∧
      (∀ i, H j i ∩ E j = W j i) ∧
      (∀ i, IsFinitePLBallPair ℝ (W j i)
        {c i (0, farArmParameter (sign j i)), c i (1, farArmParameter (sign j i))}) ∧
      Disjoint (E j) ((c false '' arm 0) ∪ (c true '' arm 0)) :=
    middle_strip_disk_complement (D.disk_ball j) c (sign j) hcPL hci hQ
      (hhalf j) hdis (hQM j)
  have hED (j : Fin 2) : E j ⊆ D.disk j := sdiff_subset
  have hES (j : Fin 2) : E j ⊆ T \ interior S := by
    intro z hz
    apply D.disk_cover.subset
    fin_cases j
    · exact Or.inl (hED 0 hz)
    · exact Or.inr (hED 1 hz)
  have hEdis : Disjoint (E 0) (E 1) := by
    refine disjoint_left.mpr ?_
    intro z hz₀ hz₁
    have hzC := D.disk_inter.subset ⟨hED 0 hz₀, hED 1 hz₁⟩
    rw [hL, hR] at hzC
    exact disjoint_left.mp (hdata 0).2.2.2.2 hz₀ hzC
  have hHsource (j : Fin 2) (i : Bool) : H j i ⊆ c i '' source :=
    image_mono (halfSource_subset_source (sign j i))
  have hcover : (c false '' source ∪ c true '' source) ∪ (E 0 ∪ E 1) =
      T \ interior S := by
    apply Subset.antisymm
    · rintro z ((hz | hz) | hz | hz)
      · exact (image_subset_iff.mpr (hcin false)) hz
      · exact (image_subset_iff.mpr (hcin true)) hz
      · exact hES 0 hz
      · exact hES 1 hz
    · intro z hz
      rcases D.disk_cover.symm.subset hz with hz | hz
      · rcases (hdata 0).2.1.symm.subset hz with (h₀ | h₁) | hE
        · exact Or.inl (Or.inl (hHsource 0 false h₀))
        · exact Or.inl (Or.inr (hHsource 0 true h₁))
        · exact Or.inr (Or.inl hE)
      · rcases (hdata 1).2.1.symm.subset hz with (h₀ | h₁) | hE
        · exact Or.inl (Or.inl (hHsource 1 false h₀))
        · exact Or.inl (Or.inr (hHsource 1 true h₁))
        · exact Or.inr (Or.inr hE)
  have hHunion (i : Bool) : H 0 i ∪ H 1 i = c i '' source := by
    rw [← image_union]
    change c i '' (halfSource (positive i) ∪ halfSource (!(positive i))) = _
    rw [halfSource_union]
  have hcontact (j : Fin 2) (i : Bool) : E j ∩ (c i '' source) = W j i := by
    apply Subset.antisymm
    · intro z hz
      rcases (hHunion i).symm.subset hz.2 with h₀ | h₁
      · fin_cases j
        · exact (hdata 0).2.2.1 i |>.subset ⟨h₀, hz.1⟩
        · have hcent := D.disk_inter.subset ⟨hhalf 0 i h₀, hED 1 hz.1⟩
          rw [hL, hR] at hcent
          exact (disjoint_left.mp (hdata 1).2.2.2.2 hz.1 hcent).elim
      · fin_cases j
        · have hcent := D.disk_inter.subset ⟨hED 0 hz.1, hhalf 1 i h₁⟩
          rw [hL, hR] at hcent
          exact (disjoint_left.mp (hdata 0).2.2.2.2 hz.1 hcent).elim
        · exact (hdata 1).2.2.1 i |>.subset ⟨h₁, hz.1⟩
    · intro z hz
      have h := ((hdata j).2.2.1 i).symm.subset hz
      exact ⟨h.2, hHsource j i h.1⟩
  exact ⟨positive, E, fun j ↦ (hdata j).1, hES, hEdis, hcover, hcontact,
    fun j i ↦ (hdata j).2.2.2.1 i⟩

end PoincareConjecture.M76.Dehn
