import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AnnulusFamily
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.BasePatch
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.RimComponents



set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76
open Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_original_collared_pair_of_rim_patches
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R)
    (S : Bool → Set X) (hS : ∀ b, S b ⊆ frontier R)
    (hdis : Disjoint (S false) (S true))
    (f : Bool → V1 × V2 → X)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) source)
    (hfi : ∀ i, InjOn (f i) source) (hfR : ∀ i, MapsTo (f i) source R)
    (hfmark : ∀ i b, MapsTo (fun z => f i (endpoint b, z)) Q (S b))
    (hpatch : ∀ b x,
      x ∈ ((fun z => f false (endpoint b, z)) '' Q) ∩
        ((fun z => f true (endpoint b, z)) '' Q) →
      ∃ d : ℝ, 0 < d ∧ ∃ u : P2 → X,
        PolyhedralPLInCharts e u (Icc (-d) d ×ˢ Icc (-d) d) ∧
        InjOn u (Icc (-d) d ×ˢ Icc (-d) d) ∧
        MapsTo u (Icc (-d) d ×ˢ Icc (-d) d) (S b) ∧ u 0 = x ∧
        (∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d,
          u z ∈ (fun w => f false (endpoint b, w)) '' Q ↔ z.2 = 0) ∧
        ∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d,
          u z ∈ (fun w => f true (endpoint b, w)) '' Q ↔ z.1 = 0) :
    ∃ g : Bool → V1 × V2 → X,
      (∀ i, PolyhedralPLInCharts e (g i) source ∧ InjOn (g i) source ∧
        MapsTo (g i) source R ∧
        (∀ z ∈ source, g i z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1) ∧
        ∀ b z, z ∈ Q → g i (endpoint b, z) = f i (endpoint b, z)) ∧
      ∀ x ∈ g false '' source ∩ g true '' source, x ∈ frontier R →
        ∃ C : OriginalSurfacePairChart e (g false '' source) (g true '' source) x true,
          (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) ∧
          ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔
            (C.coordinates z).1.2 = 0 := by
  obtain ⟨s, J, HB, c, a, rim, g, hJ, ha, ha1, hc, hci, hcR, hbase,
    hcfront, _, hg⟩ := he.exists_original_common_collared_annulus_family hR hconn f hf hfi hfR
      (fun i b z hz => hS b (hfmark i b hz))
  have hgPL (i : Bool) := (hg i).2.2.2.1
  have hgi (i : Bool) := (hg i).2.2.2.2.1
  have hgR (i : Bool) := (hg i).2.2.2.2.2.1
  have hgfront (i : Bool) := (hg i).2.2.2.2.2.2.1
  have hgend (i : Bool) := (hg i).2.2.2.2.2.2.2.1
  have hgtrace (i : Bool) := (hg i).2.2.2.2.2.2.2.2
  have hgmark (i b : Bool) : MapsTo (fun z => g i (endpoint b, z)) Q (S b) := by
    intro z hz
    change g i (endpoint b, z) ∈ S b
    rw [hgend i b z hz]
    exact hfmark i b hz
  have hrimeq (i b : Bool) : (fun z => g i (endpoint b, z)) '' Q =
      (fun z => f i (endpoint b, z)) '' Q := by
    apply image_congr
    intro z hz
    exact hgend i b z hz
  obtain ⟨A, hA, hAs⟩ := J.exists_finite_interval_product hJ ha
  have hsub : J.space ×ˢ Icc (0 : ℝ) a ⊆ J.space ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans ha1.le⟩
  have hcsmall : PolyhedralPLInCharts e c (J.space ×ˢ Icc (0 : ℝ) a) :=
    hAs ▸ hc.restrict_finite A hA (hAs.subset.trans hsub)
  have hcInj : InjOn c (J.space ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx y hy heq
    exact congrArg Subtype.val (hci.injective
      (a₁ := (⟨x, hx⟩ : J.space ×ˢ Icc (0 : ℝ) 1))
      (a₂ := (⟨y, hy⟩ : J.space ×ˢ Icc (0 : ℝ) 1)) heq)
  let D (i : Bool) := rim i false '' Q ∪ rim i true '' Q
  have hD (i : Bool) : D i ⊆ J.space := by
    rintro x (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact (hg i).2.1 false hz
    · exact (hg i).2.1 true hz
  have hztrace (i b : Bool) : (c '' (D i ×ˢ ({0} : Set ℝ))) ∩ S b =
      (fun z => f i (endpoint b, z)) '' Q :=
    common_collar_zero_trace_on_either_component S hdis c (rim i)
      (fun b z => f i (endpoint b, z)) ((hg i).2.2.1) (hfmark i) b
  refine ⟨g, (fun i => ⟨hgPL i, hgi i, hgR i, hgfront i, hgend i⟩), ?_⟩
  intro x hx hxR
  obtain ⟨b, hb⟩ := proper_annuli_boundary_point_on_common_rim S hdis g hgfront hgmark hx hxR
  rw [hrimeq false b, hrimeq true b] at hb
  obtain ⟨d, hd, u, hu, hui, huS, hu0, huaxis₀, huaxis₁⟩ := hpatch b x hb
  obtain ⟨C, hCR, hCfront⟩ := he.exists_original_common_collar_chart_of_base_patch
    (image_subset_iff.mpr (hgR false)) (image_subset_iff.mpr (hgR true)) (hS b)
    hd u hu hui huS huaxis₀ huaxis₁ HB ha c hcsmall (hcInj.mono hsub) hbase
    (hcR.mono_left hsub) (fun z hz => hcfront z (hsub hz)) (hD false) (hD true)
    (hgtrace false) (hgtrace true) (hztrace false b) (hztrace true b)
  exact hu0 ▸ ⟨C, hCR, hCfront⟩

end PoincareConjecture.M76
