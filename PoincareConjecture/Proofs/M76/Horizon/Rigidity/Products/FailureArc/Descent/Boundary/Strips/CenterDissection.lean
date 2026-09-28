import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Cuts.Spanning
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.Sides








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_spanning_strip_center_dissection
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
    ∃ (D : NestedShellDissection S T) (positive : Bool → Bool),
      D.left = c false '' arm 0 ∧ D.right = c true '' arm 0 ∧
      D.x = c false (0, 0) ∧ D.y = c true (0, 0) ∧
      D.a = c false (1, 0) ∧ D.b = c true (1, 0) ∧
      (∀ i, c i '' halfSource (positive i) ⊆ D.disk 0) ∧
      (∀ i, c i '' halfSource (!(positive i)) ⊆ D.disk 1) := by
  have hcenter : arm 0 ⊆ source :=
    (arm_zero_subset_halfSource false).trans (halfSource_subset_source false)
  have h0 : ((0, 0) : P2) ∈ source := by norm_num [source]
  have h1 : ((1, 0) : P2) ∈ source := by norm_num [source]
  have hball (i : Bool) : IsFinitePLBallPair ℝ (c i '' arm 0)
      {c i (0, 0), c i (1, 0)} := by
    have h := (exists_arm_parameter 0).1.image_of_subset (hcPL i) hcenter (hci i)
    simpa only [image_pair] using h
  have hin (i : Bool) : c i '' arm 0 ∩ S = {c i (1, 0)} := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzS⟩
      have hfront : c i z ∈ frontier S :=
        ⟨subset_closure hzS, (hcin i (hcenter hz)).2⟩
      have he : z = (1, 0) := Prod.ext ((hinner i z (hcenter hz)).mp hfront) hz.2
      exact congrArg (c i) he
    · rintro rfl
      exact ⟨mem_image_of_mem (c i) (by norm_num [arm]),
        hS.1 ((hinner i (1, 0) h1).mpr rfl)⟩
  have hproper (i : Bool) : (c i '' arm 0) \ {c i (0, 0)} ⊆ interior T := by
    rintro x ⟨⟨z, hz, rfl⟩, hn⟩
    by_contra hnot
    have hfront : c i z ∈ frontier T :=
      ⟨subset_closure (hcin i (hcenter hz)).1, hnot⟩
    have he : z = (0, 0) := Prod.ext ((houter i z (hcenter hz)).mp hfront) hz.2
    exact hn (congrArg (c i) he)
  obtain ⟨D, hx, hy, ha, hb, hL, hR⟩ := exists_shell_dissection_with_spanning_sides
    hS hT hST (hball false) (by simpa only [pair_comm] using hball true)
    ((hinner false (1, 0) h1).mpr rfl) ((hinner true (1, 0) h1).mpr rfl)
    ((houter false (0, 0) h0).mpr rfl) ((houter true (0, 0) h0).mpr rfl)
    (hin false) (hin true) (hproper false) (hproper true)
    (hdis.mono (image_mono hcenter) (image_mono hcenter))
  have hseams (i : Bool) : c i '' arm 0 ⊆ D.left ∪ D.right := by
    rw [hL, hR]
    cases i
    · exact subset_union_left
    · exact subset_union_right
  have hwhole (i : Bool) : c i '' source ⊆ D.disk 0 ∪ D.disk 1 := by
    rw [D.disk_cover]
    exact image_subset_iff.mpr (hcin i)
  have htrace (i : Bool) : (c i '' source) ∩ (D.disk 0 ∩ D.disk 1) = c i '' arm 0 := by
    rw [D.disk_inter, hL, hR]
    cases i
    · ext x
      constructor
      · rintro ⟨hx, hxC | hxC⟩
        · exact hxC
        · exact (disjoint_left.mp hdis hx ((image_mono hcenter) hxC)).elim
      · intro hx
        exact ⟨(image_mono hcenter) hx, Or.inl hx⟩
    · ext x
      constructor
      · rintro ⟨hx, hxC | hxC⟩
        · exact (disjoint_left.mp hdis ((image_mono hcenter) hxC) hx).elim
        · exact hxC
      · intro hx
        exact ⟨(image_mono hcenter) hx, Or.inr hx⟩
  have hsides (i : Bool) : ∃ b : Bool,
      c i '' halfSource b ⊆ D.disk 0 ∧ c i '' halfSource (!b) ⊆ D.disk 1 :=
    exists_opposite_strip_sides_of_center_trace (D.disk_ball 0) (D.disk_ball 1)
      (c i) (hcPL i) (hci i) (hwhole i) (htrace i)
      ((hseams i).trans subset_union_right) ((hseams i).trans subset_union_right)
  choose positive hpos hneg using hsides
  exact ⟨D, positive, hL, hR, hx, hy, ha, hb, hpos, hneg⟩

end PoincareConjecture.M76.Dehn
