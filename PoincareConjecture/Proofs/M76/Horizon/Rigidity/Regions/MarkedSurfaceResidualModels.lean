import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.MarkedSurfaceResidualCount
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLCubeSphereModel
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteFrontierComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedFiniteModel

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem nonempty_residual_model_of_marked_surface
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {N F : Set X}
    (s : Finset N) (K : SimplicialComplex ℝ (s → ℝ × V3)) (hK : K.faces.Finite)
    (g : (s → ℝ × V3) → X) (u : X → (s → ℝ × V3))
    (hu : Continuous u) (hui : InjOn u N)
    (huPL : ∀ i, LocallyPiecewiseAffineOn (u ∘ (e i).symm) (e i).target)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hinverse : ∀ z ∈ K.space, u (g z) = z)
    (himage : g '' K.space = F) (hne : F.Nonempty)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, q.card = 3 ∧ t ⊆ q)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ t ∈ K.faces, t.card = 2 →
      let n := {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard
      n = 1 ∨ n = 2) :
    Nonempty (FrontierResidualModel e N F) := by
  classical
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let S (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) : Set X :=
    g '' (K.edgeComponentComplex C).space
  have hsub (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      (K.edgeComponentComplex C).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le C)
  have hfinite (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      (K.edgeComponentComplex C).faces.Finite := hK.subset (K.edgeComponentComplex_le C)
  have hcompact (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) : IsCompact (S C) :=
    ((K.edgeComponentComplex C).isCompact_space_of_finite (hfinite C)).image_of_continuousOn
      (hg.continuousOn.mono (hsub C))
  have hconn (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) : IsConnected (S C) :=
    (K.edgeComponentComplex_isPathConnected C).isConnected.image g
      (hg.continuousOn.mono (hsub C))
  have hdisjoint : Pairwise fun C D => Disjoint (S C) (S D) := by
    intro C D hCD
    apply disjoint_left.mpr
    rintro x ⟨v, hv, hvx⟩ ⟨w, hw, hwx⟩
    have hvw := hgi (hsub C hv) (hsub D hw) (hvx.trans hwx.symm)
    exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_space hCD)
      hv (hvw.symm ▸ hw)
  have hunion : (⋃ C, S C) = F := by
    change (⋃ C, g '' (K.edgeComponentComplex C).space) = F
    rw [← image_iUnion, K.iUnion_edgeComponentComplex_space, himage]
  have hF : IsClosed F := by
    rw [← himage]
    exact ((K.isCompact_space_of_finite hK).image_of_continuousOn hg.continuousOn).isClosed
  obtain ⟨n, pick, hn, hselected, hcomponents⟩ :=
    exists_indexed_components_of_closed_partition S (fun C => (hcompact C).isClosed)
      hconn hdisjoint isClosed_empty hF (empty_disjoint F)
      (hunion.trans (empty_union F).symm) hne
  obtain ⟨r, hr⟩ := K.exists_component_residual_counts_of_marked_surface hK hpure hlinks hcofaces
  refine ⟨{
    vertices := s
    coordinates := u
    complex := K
    map := g
    count := n
    pick := pick
    components := fun i => S (pick i)
    residual := fun i => r (pick i)
    coordinates_continuous := hu
    coordinates_injective := hui
    coordinates_pl := huPL
    finite := hK
    dimension := ?_
    pl := hg
    injective := hgi
    inverse := hinverse
    positive := hn
    images := fun _ => rfl
    cover := hselected
    disjoint := fun _ _ hij => hdisjoint (fun h => hij (pick.injective h))
    component := ?_
    euler := fun i => (hr (pick i)).1
    zero_sphere := ?_
  }⟩
  · intro t ht
    obtain ⟨q, _, hqc, htq⟩ := hpure t ht
    exact (Finset.card_le_card htq).trans_eq hqc
  · intro i
    exact ⟨hcompact (pick i), hconn (pick i),
      fun _ hx => hselected.subset (mem_iUnion.mpr ⟨i, hx⟩), hcomponents i⟩
  · intro i hz
    obtain ⟨H, hH⟩ := (hr (pick i)).2.2 hz
    have hcv : Convex ℝ (TriangularRoofModel.halfBall 1) := by
      rw [TriangularRoofModel.halfBall_eq_halfspaces]
      simp only [ofPred_forall]
      exact convex_iInter fun j => (convex_Iic 0).affine_preimage (TriangularRoofModel.halfBallForms 1 j)
    have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by simp [Module.finrank_prod]
    obtain ⟨b, hb⟩ := hH.exists_unit_cube_sphere_model
      (TriangularRoofModel.isCompact_halfBall (Or.inl rfl)) hcv
      (TriangularRoofModel.interior_halfBall_nonempty (h := 1) (Or.inl rfl)) hdim
    exact exists_chartwisePLSphere_image K hg hgi (hsub (pick i)) b hb

theorem nonempty_residual_model_of_compact_marked_surface
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Nonempty X]
    (e : ι → OpenPartialHomeomorph X V3) (hX : IsCompact (univ : Set X))
    {R S M : Set X} (he : PLDomain e R) (hS : IsCompact S) (hne : S.Nonempty)
    (hlocal : ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source M) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ M ↔ psi (T y) = 0)) :
    Nonempty (FrontierResidualModel e univ S) := by
  classical
  obtain ⟨s, F, K, B, g, hF, hFi, hFPL, hK, _, _, _, _, hg, hgi,
    hinv, himage, hpure, hcofaces, hlinks⟩ :=
    exists_original_marked_surface_finite_incidence e hX he hS hlocal
  apply nonempty_residual_model_of_marked_surface s K hK g F hF hFi.injOn hFPL
    hg hgi hinv himage hne hpure hlinks
  intro t ht htc
  dsimp only
  rw [hcofaces t ht htc]
  split_ifs <;> simp

end PoincareConjecture.M76
