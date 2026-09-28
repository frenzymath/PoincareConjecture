import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Assignment.Cover
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Assignment.Order
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.ProtectedSubcomplex
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.FiniteHistory










set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}



structure OriginalRelativeNormalization (step : Step s t)
    (K : SimplicialComplex ℝ V) (j : V → t.Carrier) (R : Set M) (boundary : Set V) where
  source : SimplicialComplex ℝ V
  source_finite : source.faces.Finite
  subdivision : source.IsSubdivision K
  fixed : SimplicialComplex ℝ V
  protected_le : fixed ≤ source
  protected_full : ∀ a ∈ source.faces,
    (∀ v ∈ a, v ∈ fixed.vertices) → a ∈ fixed.faces
  boundary_protected : boundary ⊆ fixed.space
  protected_fiber : ∀ x ∈ fixed.space, ∀ y ∈ K.space,
    step.projection (step.inclusion (j x)) = step.projection (step.inclusion (j y)) → x = y
  length : ℕ
  face : Fin length → Finset V
  face_injective : Function.Injective face
  face_range : range face = source.faces \ fixed.faces
  prior : ℕ → SimplicialComplex ℝ V
  prefix_mono : Monotone prior
  prefix_le : ∀ k, prior k ≤ source
  prefix_zero : prior 0 = fixed
  prefix_last : prior length = source
  prefix_succ : ∀ i : Fin length,
    (prior (i.val + 1)).space = (prior i.val).space ∪ convexHull ℝ (face i : Set V)
  prefix_frontier : ∀ i : Fin length,
    intrinsicFrontier ℝ (convexHull ℝ (face i : Set V)) ⊆ (prior i.val).space
  center : source.faces → V
  center_mem : ∀ a, center a ∈ source.space
  box : ∀ a, RelativeChartBox step R (j (center a))
  box_interior : ∀ a : source.faces, a.val ∉ fixed.faces →
    (box a).upper.source ⊆ interior (t.projection ⁻¹' R)
  states : ℕ → RelativeSurfaceState t source (fun a ↦ (box a).neighborhood) R boundary
  initial : (states 0).map = j
  motions : ∀ i : Fin length,
    RelativeFaceMotionData step source (prior i.val) (prior (i.val + 1)) (states i.val).map
      (box ⟨face i, (face_range.subset ⟨i, rfl⟩).1⟩).upper
      (box ⟨face i, (face_range.subset ⟨i, rfl⟩).1⟩).lower
      (box ⟨face i, (face_range.subset ⟨i, rfl⟩).1⟩).support
      (fun a ↦ (box a).neighborhood) R
  transition : ∀ i : Fin length,
    (states (i.val + 1)).map = (motions i).ambient 1 ∘ (states i.val).map
  stable : ∀ i k, i ≤ k → k ≤ length →
    EqOn (states k).map (states i).map (prior i).space
  fixes_protected : ∀ k ≤ length, EqOn (states k).map j fixed.space



theorem Step.nonempty_original_relative_normalization (step : Step s t)
    {R : Set M} (he : PoincareConjecture.M76.PLDomain e R)
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : IsEmbedding (fun x : K.space ↦ j x))
    (hjR : MapsTo j K.space (t.projection ⁻¹' R))
    (boundary : Set V) (hb : IsCompact boundary) (hbK : boundary ⊆ K.space)
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ boundary)
    (hrim : InjOn (t.projection ∘ j) boundary) :
    Nonempty (OriginalRelativeNormalization step K j R boundary) := by
  classical
  obtain ⟨P, K₁, A₁, _, hK₁, hsub₁, hA₁K₁, hA₁s, hbP, hbA₁, _, _, hfiber⟩ :=
    step.exists_protected_source_subcomplex K hK hj hji boundary hb hbK R hproper hrim
  have hj₁ : PolyhedralPLInCharts t.charts j K₁.space := by
    simpa only [hsub₁.space_eq] using hj
  have hjR₁ : MapsTo j K₁.space (t.projection ⁻¹' R) := by
    simpa only [hsub₁.space_eq] using hjR
  have hproper₁ : ∀ x ∈ K₁.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ boundary := by
    simpa only [hsub₁.space_eq] using hproper
  have hA₁s' : A₁.space = K₁.space ∩ P.space := by
    simpa only [hsub₁.space_eq] using hA₁s
  obtain ⟨K₂, A₂, hK₂, hsub₂, hA₂K₂, hA₂s, hfull, center, box, hretain, hinside⟩ :=
    step.exists_relative_face_chart_cover he K₁ A₁ P hK₁ hA₁K₁ hA₁s' hbP
      hj₁ hjR₁ hproper₁
  obtain ⟨n, face, hfi, hfr, hbefore⟩ := K₂.exists_relative_face_order A₂ hK₂
  obtain ⟨prior, hmono, hprefix, hzero, hlast, hsucc, hfront⟩ :=
    K₂.exists_relative_face_prefixes A₂ hK₂ hA₂K₂ face hfr hbefore
  have hface (i : Fin n) : face i ∈ K₂.faces := (hfr.subset ⟨i, rfl⟩).1
  let atFace (i : Fin n) : K₂.faces := ⟨face i, hface i⟩
  let N (a : K₂.faces) : Set t.Carrier := (box a).neighborhood
  have hspace : K₂.space = K.space := hsub₂.space_eq.trans hsub₁.space_eq
  let initial : RelativeSurfaceState t K₂ N R boundary :=
    { map := j
      original_PL := by simpa only [hspace] using hj
      embedding := hji.comp (Homeomorph.setCongr hspace).isEmbedding
      region := by simpa only [hspace] using hjR
      proper := by simpa only [hspace] using hproper
      retained := hretain }
  obtain ⟨states, hinit, hsteps, hstable, hfix⟩ :=
    step.exists_relative_finite_face_history K₂ hK₂ face hface prior hmono
      (fun k _ ↦ (hprefix k).2.1) hsucc R boundary
      (fun i ↦ (box (atFace i)).upper) (fun i ↦ (box (atFace i)).lower)
      (fun i ↦ (box (atFace i)).support)
      (fun i ↦ (box (atFace i)).upper_compatible)
      (fun i ↦ (box (atFace i)).lower_compatible)
      (fun i ↦ (box (atFace i)).finite_support)
      (fun i ↦ (box (atFace i)).convex_support)
      (fun i ↦ (box (atFace i)).support_target)
      (fun i ↦ (box (atFace i)).support_target.trans
        (box (atFace i)).targets.subset)
      (fun i ↦ hinside (atFace i) (hfr.subset ⟨i, rfl⟩).2)
      N (fun a ↦ (box a).neighborhood_open)
      (fun i ↦ (box (atFace i)).neighborhood_support) initial
  choose motion hmotion using (fun i : Fin n ↦ hsteps i.val i.isLt)
  refine ⟨{
    source := K₂
    source_finite := hK₂
    subdivision := hsub₂.trans hsub₁
    fixed := A₂
    protected_le := hA₂K₂
    protected_full := hfull
    boundary_protected := hbA₁.trans hA₂s.symm.subset
    protected_fiber := fun x hx y hy hxy ↦ hfiber x (hA₂s.subset hx) y hy hxy
    length := n
    face := face
    face_injective := hfi
    face_range := hfr
    prior := prior
    prefix_mono := hmono
    prefix_le := fun k ↦ (hprefix k).2.1
    prefix_zero := hzero
    prefix_last := hlast
    prefix_succ := hsucc
    prefix_frontier := hfront
    center := fun a ↦ center a
    center_mem := fun a ↦ hsub₂.space_eq.symm.subset (center a).property
    box := box
    box_interior := hinside
    states := states
    initial := congrArg RelativeSurfaceState.map hinit
    motions := motion
    transition := hmotion
    stable := hstable
    fixes_protected := ?_ }⟩
  intro k hk x hx
  exact hfix k hk (hzero.symm ▸ hx)

end Geometry.OriginalPLTower
