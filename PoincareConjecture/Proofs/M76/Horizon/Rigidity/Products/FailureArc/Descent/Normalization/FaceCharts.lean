import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.ChartCubes
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteMarkedFaceCover
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartRegion

set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_marked_surface_face_charts
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (K₀ A₀ : SimplicialComplex ℝ V) (hK₀ : K₀.faces.Finite) (hA₀ : A₀.faces.Finite)
    (hA₀K₀ : A₀.space ⊆ K₀.space)
    (he : PoincareConjecture.M76.PLDomain e R)
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K₀.space)
    (hji : IsEmbedding (fun x : K₀.space => j x))
    (hjR : MapsTo j K₀.space (t.projection ⁻¹' R))
    (hproper : ∀ x : K₀.space, j x ∈ frontier (t.projection ⁻¹' R) ↔ (x : V) ∈ A₀.space)
    (hjF : ∀ x : A₀.space, t.projection (j x) ∈ Fmark) :
    ∃ (W : Set M) (K A : SimplicialComplex ℝ V),
      IsOpen W ∧ Fmark = frontier R ∩ W ∧
      K.faces.Finite ∧ K.space = K₀.space ∧ A.faces.Finite ∧ A ≤ K ∧ A.space = A₀.space ∧
      (∀ σ ∈ K.faces, (∀ v ∈ σ, v ∈ A.vertices) → σ ∈ A.faces) ∧
      ∀ σ ∈ K.faces,
        ∃ (x : K₀.space) (Q : OpenPartialHomeomorph t.Carrier V3)
          (B : OpenPartialHomeomorph s.Carrier V3)
          (a : ℝ) (J : SimplicialComplex ℝ V3),
          j x ∈ Q.source ∧ InjOn (step.projection ∘ step.inclusion) Q.source ∧
          (∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
          (∀ l, (s.charts l).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
          Q.target = B.target ∧
          (∀ y, Q y = B (step.projection (step.inclusion y))) ∧
          MapsTo (step.projection ∘ step.inclusion) Q.source B.source ∧
          EqOn ((step.projection ∘ step.inclusion) ∘ Q.symm) B.symm B.target ∧
          0 < a ∧ J.faces.Finite ∧ J.space = closedBall (Q (j x)) (3 * a) ∧
          J.space ⊆ Q.target ∧
          closure (ball (Q (j x)) a) ⊆ ball (Q (j x)) (2 * a) ∧
          closure (ball (Q (j x)) (2 * a)) ⊆ interior J.space ∧
          (σ ∈ A.faces → Q.source ⊆ t.projection ⁻¹' W) ∧
          (B.source ⊆ interior (s.projection ⁻¹' R) ∨
            ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
              ell.contLinear v = 1 ∧ ell (Q (j x)) = 0 ∧
              (∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y)) ∧
              ∀ y ∈ B.source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B y) = 0) ∧
          (∀ z ∈ convexHull ℝ (σ : Set V),
            j z ∈ Q.source ∧ Q (j z) ∈ ball (Q (j x)) a) ∧
          InjOn (step.projection ∘ step.inclusion ∘ j) (convexHull ℝ (σ : Set V)) := by
  classical
  obtain ⟨W, hW, hFW⟩ := exists_open_frontier_mark hF hopen
  have hpoint (x : K₀.space) := step.exists_marked_surface_chart_cube he hW (hjR x.property)
    (fun hx => (hFW.subset (hjF ⟨x, (hproper x).mp hx⟩)).2)
  choose Q B a J hxQ hinj hQ hB htarget hval hmaps hinv ha hJ hJs hJQ
    hsmall hlarge hinside hmark hmodel using hpoint
  let U (x : K₀.space) : Set K₀.space := (fun z : K₀.space => j z) ⁻¹'
    ((Q x).source ∩ (Q x) ⁻¹' ball (Q x (j x)) (a x))
  have hjc : Continuous (fun z : K₀.space => j z) :=
    hj.continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)
  have hU (x : K₀.space) : IsOpen (U x) :=
    ((Q x).isOpen_inter_preimage isOpen_ball).preimage hjc
  have hcover (x : K₀.space) : ∃ y : K₀.space, x ∈ U y :=
    ⟨x, hxQ x, mem_ball_self (ha x)⟩
  obtain ⟨K, A, hK, hKK₀, hA, hAK, hAs, hfull, hfaces⟩ :=
    K₀.exists_finite_marked_face_cover A₀ hK₀ hA₀ hA₀K₀ U hU hcover
  have hKs := hKK₀.space_eq
  refine ⟨W, K, A, hW, hFW, hK, hKs, hA, hAK, hAs, hfull, ?_⟩
  intro σ hσ
  obtain ⟨x, hx⟩ := hfaces σ hσ
  have hσK₀.space : convexHull ℝ (σ : Set V) ⊆ K₀.space :=
    (K.convexHull_subset_space hσ).trans hKs.subset
  have hface : ∀ z ∈ convexHull ℝ (σ : Set V),
      j z ∈ (Q x).source ∧ Q x (j z) ∈ ball (Q x (j x)) (a x) :=
    fun z hz => hx ⟨z, hσK₀.space hz⟩ hz
  refine ⟨x, Q x, B x, a x, J x, hxQ x, hinj x, hQ x, hB x, htarget x,
    hval x, hmaps x, hinv x, ha x, hJ x, hJs x, hJQ x, hsmall x, hlarge x,
    ?_, hmodel x, hface, ?_⟩
  · intro hσA
    apply hmark x
    refine ⟨subset_closure (hjR x.property), ?_⟩
    intro hxint
    obtain ⟨z, hz⟩ := K.nonempty_of_mem_faces hσ
    have hzconv : z ∈ convexHull ℝ (σ : Set V) := subset_convexHull ℝ _ hz
    have hzrim : z ∈ A₀.space := hAs.subset (A.convexHull_subset_space hσA hzconv)
    have hzfront := (hproper ⟨z, hσK₀.space hzconv⟩).mpr hzrim
    exact hzfront.2 (hinside x hxint (hface z hzconv).1)
  · intro u hu v hv huv
    have hjuv : j u = j v := (hinj x) (hface u hu).1 (hface v hv).1 huv
    have heq : (⟨u, hσK₀.space hu⟩ : K₀.space) = ⟨v, hσK₀.space hv⟩ := hji.injective hjuv
    exact congrArg Subtype.val heq

end Geometry.OriginalPLTower
