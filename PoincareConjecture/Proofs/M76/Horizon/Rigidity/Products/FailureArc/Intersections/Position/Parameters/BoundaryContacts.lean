import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem finite_boundary_contacts_of_pair_charts
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T R : Set X}
    (hcompact : IsCompact ((S ∩ T) ∩ frontier R))
    (hcharts : ∀ y ∈ (S ∩ T) ∩ frontier R,
      ∃ C : OriginalSurfacePairChart e S T y true,
        ∀ z ∈ C.coordinates.source,
          C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0) :
    ((S ∩ T) ∩ frontier R).Finite := by
  classical
  let Contact := (S ∩ T) ∩ frontier R
  choose C hfront using fun p : Contact => hcharts p p.property
  let U (p : Contact) : Set X :=
    (C p).chart.source ∩ (C p).chart ⁻¹' (C p).coordinates.source
  have hU (p : Contact) : IsOpen (U p) :=
    (C p).chart.isOpen_inter_preimage (C p).coordinates.open_source
  have hpU (p : Contact) : (p : X) ∈ U p :=
    ⟨(C p).center_source, (C p).center_coordinates⟩
  have hlocal (p : Contact) (y : X) (hy : y ∈ Contact) (hyU : y ∈ U p) : y = p := by
    have hS := ((C p).first_surface _ hyU.2).mp
      (by simpa only [(C p).chart.left_inv hyU.1] using hy.1.1)
    have hT := ((C p).second_surface _ hyU.2).mp
      (by simpa only [(C p).chart.left_inv hyU.1] using hy.1.2)
    have hR := (hfront p _ hyU.2).mp
      (by simpa only [(C p).chart.left_inv hyU.1] using hy.2)
    have hzero : (C p).coordinates ((C p).chart y) = 0 :=
      Prod.ext (Prod.ext hT.1 hR) hS.1
    exact (C p).chart.injOn hyU.1 (C p).center_source
      ((C p).coordinates.injOn hyU.2 (C p).center_coordinates
        (hzero.trans (C p).center_zero.symm))
  obtain ⟨I, hI⟩ := hcompact.elim_finite_subcover U hU
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hpU ⟨y, hy⟩⟩)
  apply (I.finite_toSet.image (Subtype.val : Contact → X)).subset
  intro y hy
  obtain ⟨p, hp, hyU⟩ := mem_iUnion₂.mp (hI hy)
  exact ⟨p, hp, (hlocal p y hy hyU).symm⟩

theorem finite_source_rim_contacts_of_pair_charts
    {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {K rim : Set E} (hK : IsCompact K) {g : E → X}
    (hg : ContinuousOn g K) (hgi : InjOn g K)
    {S R : Set X} (hS : IsClosed S)
    (hproper : ∀ x ∈ K, g x ∈ frontier R ↔ x ∈ rim)
    (hboundary : ∀ x ∈ K ∩ rim, g x ∈ S →
      ∃ C : OriginalSurfacePairChart e S (g '' K) (g x) true,
        ∀ z ∈ C.coordinates.source,
          C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0) :
    {x | x ∈ K ∩ rim ∧ g x ∈ S}.Finite := by
  have hcompact : IsCompact ((S ∩ (g '' K)) ∩ frontier R) :=
    ((hK.image_of_continuousOn hg).inter_left hS).inter_right isClosed_frontier
  have hfinite := finite_boundary_contacts_of_pair_charts hcompact (by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy.1.2
    subst y
    exact hboundary x ⟨hx, (hproper x hx).mp hy.2⟩ hy.1.1)
  apply Set.Finite.of_finite_image (hfinite.subset ?_) (hgi.mono (fun x hx => hx.1.1))
  rintro y ⟨x, hx, rfl⟩
  exact ⟨⟨hx.2, mem_image_of_mem g hx.1.1⟩, (hproper x hx.1.1).mpr hx.1.2⟩

end PoincareConjecture.M76
