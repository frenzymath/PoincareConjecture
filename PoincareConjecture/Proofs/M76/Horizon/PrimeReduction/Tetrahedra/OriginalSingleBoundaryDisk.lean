import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SingleBoundaryPiece
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalPolygonCut
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_original_single_boundary_piece_disk
    {X E ι γ : Type*} [TopologicalSpace X] [T2Space X] [Finite γ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S B : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hB : IsClosed B) (P : γ → Set X) (hP : ∀ c, IsClosed (P c))
    (hdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hcover : S ∩ B ⊆ ⋃ c, P c)
    (c : γ) (hcS : P c ⊆ S) (hcB : P c ⊆ B)
    {n : ℕ} (L : Polygon E (n + 3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) {g : E → X}
    (hg : PolyhedralPLInCharts e g (L.boundary ℝ))
    (hgi : InjOn g (L.boundary ℝ))
    (hfront : P c ∩ frontier B = g '' L.boundary ℝ)
    (hne : (P c \ g '' L.boundary ℝ).Nonempty) (hout : ¬ S ⊆ B) :
    ∃ d q : Set V3, IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ Sphere ∧
      s.map '' d = P c ∧ s.map '' q = g '' L.boundary ℝ := by
  have hLS : g '' L.boundary ℝ ⊆ S :=
    hfront.symm.subset.trans (inter_subset_left.trans hcS)
  obtain ⟨x,hxc,hxr⟩ := hne
  obtain ⟨m,R,d,hRi,hRe,hd,hwhole,hinter,hrim⟩ :=
    s.exists_original_polygon_parameter_cut he L hL hLi hg hgi hLS ⟨x,hcS hxc⟩ hxr
  have hdS (i : Fin 2) : d i ⊆ Sphere := by
    fin_cases i
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hrS : R.boundary ℝ ⊆ Sphere := (hd 0).1.trans (hdS 0)
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hswhole : s.map '' Sphere = S := by
    apply Subset.antisymm
    · rintro _ ⟨y,hy,rfl⟩
      rw [s.map_eq ⟨y,hy⟩]
      exact (s.parametrization ⟨y,hy⟩).property
    · intro y hy
      refine ⟨s.parametrization.symm ⟨y,hy⟩,(s.parametrization.symm ⟨y,hy⟩).property,?_⟩
      rw [s.map_eq]
      exact congrArg Subtype.val (s.parametrization.apply_symm_apply ⟨y,hy⟩)
  have hdiff (i : Fin 2) : s.map '' (d i \ R.boundary ℝ) =
      (s.map '' d i) \ (g '' L.boundary ℝ) := by
    rw [←hrim]
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨z,hz.1,rfl⟩,?_⟩
      rintro ⟨w,hw,hwz⟩
      exact hz.2 (hsi (hrS hw) (hdS i hz.1) hwz ▸ hw)
    · rintro ⟨⟨z,hz,rfl⟩,hnot⟩
      exact ⟨z,⟨hz,fun hr => hnot ⟨z,hr,rfl⟩⟩,rfl⟩
  let D (b : Bool) := s.map '' d (if b then 1 else 0)
  have hDwhole : D false ∪ D true = S := by
    change s.map '' d 0 ∪ s.map '' d 1 = S
    rw [←image_union,hwhole,hswhole]
  have hDinter : D false ∩ D true = g '' L.boundary ℝ := by
    change s.map '' d 0 ∩ s.map '' d 1 = _
    rw [←image_inter_on (fun x hx y hy hxy => hsi (hdS 1 hx) (hdS 0 hy) hxy),
      hinter,hrim]
  have hDconn (b : Bool) : IsConnected (D b \ g '' L.boundary ℝ) := by
    rw [←hdiff]
    exact (hd _).isConnected_sdiff.image s.map
      (s.piecewiseAffine.continuousOn.mono (sdiff_subset.trans (hdS _)))
  have hDcl (b : Bool) : closure (D b \ g '' L.boundary ℝ) = D b := by
    let i : Fin 2 := if b then 1 else 0
    change closure ((s.map '' d i) \ g '' L.boundary ℝ) = s.map '' d i
    rw [←hdiff]
    apply Subset.antisymm
    · exact closure_minimal (image_mono sdiff_subset)
        (((hd i).isCompact.image_of_continuousOn
          (s.piecewiseAffine.continuousOn.mono (hdS i))).isClosed)
    · have hc : ContinuousOn s.map (closure (d i \ R.boundary ℝ)) := by
        rw [(hd i).closure_sdiff]
        exact s.piecewiseAffine.continuousOn.mono (hdS i)
      simpa only [(hd i).closure_sdiff] using hc.image_closure
  obtain ⟨b,hb⟩ := closed_piece_eq_side_of_single_boundary hB s.isCompact.isClosed
    P hP hdis hcover c hcS hcB hfront ⟨x,hxc,hxr⟩ D hDwhole hDinter hDconn hDcl hout
  exact ⟨d (if b then 1 else 0),R.boundary ℝ,hd _,hdS _,hb.symm,hrim⟩

end PoincareConjecture.M76
