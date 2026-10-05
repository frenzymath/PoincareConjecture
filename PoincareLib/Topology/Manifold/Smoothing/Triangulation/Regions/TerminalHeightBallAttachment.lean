import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.PLBallActualDiskAttachment
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.HeightSeparatedSets

/-!
# Joining terminal height fillings along their actual disk

Opposite height bounds force the exact common disk. The
complete complementary boundaries are the original lower
and upper surface pieces, so their union is the whole
original surface. See Alexander 1924, pp. 6--8 and M76
derivation 248g.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Lower and upper three-ball fillings separated by height
join to a three-ball whose exact boundary is the original
whole surface. The actual shared planar disk and points on
both strict sides are retained. This asserts no exterior
ball for their union. See Alexander pp. 6--8 and derivation248g. -/
theorem IsFinitePLBallPair.union_of_height_cut_contact
    {B T s d : Set E} (A : E → ℝ) {c : ℝ}
    (hB : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) B (d ∪ (s ∩ {x | A x ≤ c})))
    (hT : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) T (d ∪ (s ∩ {x | c ≤ A x})))
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (s ∩ {x | A x = c}))
    (hdplane : d ⊆ {x | A x = c}) (hdcontact : d ∩ s = s ∩ {x | A x = c})
    (hBbelow : B ⊆ {x | A x ≤ c}) (hTabove : T ⊆ {x | c ≤ A x})
    (hTcut : T ∩ {x | A x = c} = d)
    (hlower : (s ∩ {x | A x < c}).Nonempty)
    (hupper : (s ∩ {x | c < A x}).Nonempty) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (B ∪ T) s := by
  have hBT : B ∩ T = d := inter_eq_of_height_separation A hBbelow hTabove hTcut
    (subset_union_left.trans hB.1)
  have hlout : ((d ∪ (s ∩ {x | A x ≤ c})) \ d).Nonempty := by
    obtain ⟨x, hxs, hxc⟩ := hlower
    change A x < c at hxc
    refine ⟨x, Or.inr ⟨hxs, hxc.le⟩, ?_⟩
    intro hx
    exact hxc.ne (hdplane hx)
  have huout : ((d ∪ (s ∩ {x | c ≤ A x})) \ d).Nonempty := by
    obtain ⟨x, hxs, hcx⟩ := hupper
    change c < A x at hcx
    refine ⟨x, Or.inr ⟨hxs, hcx.le⟩, ?_⟩
    intro hx
    exact hcx.ne' (hdplane hx)
  have hboundary (u : Set E) (hus : u ⊆ s) (hqu : s ∩ {x | A x = c} ⊆ u) :
      (d ∪ u) \ (d \ (s ∩ {x | A x = c})) = u := by
    ext x
    have hu := @hus x
    have hq := @hqu x
    have hds : x ∈ d → x ∈ s → x ∈ s ∩ {x | A x = c} :=
      fun hxd hxs => hdcontact.subset ⟨hxd, hxs⟩
    change ((x ∈ d ∨ x ∈ u) ∧ ¬ (x ∈ d ∧ x ∉ s ∩ {x | A x = c})) ↔ x ∈ u
    tauto
  have hleft : (d ∪ (s ∩ {x | A x ≤ c})) \ (d \ (s ∩ {x | A x = c})) =
      s ∩ {x | A x ≤ c} :=
    hboundary _ inter_subset_left (fun _ hx => ⟨hx.1, hx.2.le⟩)
  have hright : (d ∪ (s ∩ {x | c ≤ A x})) \ (d \ (s ∩ {x | A x = c})) =
      s ∩ {x | c ≤ A x} :=
    hboundary _ inter_subset_left (fun _ hx => ⟨hx.1, hx.2.symm.le⟩)
  have hcover : (s ∩ {x | A x ≤ c}) ∪ (s ∩ {x | c ≤ A x}) = s := by
    ext x
    have h := le_total (A x) c
    change ((x ∈ s ∧ A x ≤ c) ∨ (x ∈ s ∧ c ≤ A x)) ↔ x ∈ s
    tauto
  have hball := hB.union_of_actual_disk_contact hT hd subset_union_left subset_union_left
    hlout huout hBT
  rwa [hleft, hright, hcover] at hball

end Set
