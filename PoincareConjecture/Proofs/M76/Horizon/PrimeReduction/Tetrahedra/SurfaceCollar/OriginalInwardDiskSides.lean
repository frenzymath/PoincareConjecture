import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.InwardDiskSides

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "D" => closedBall (0 : P2) 1
local notation "rim" => sphere (0 : P2) 1

theorem ChartwisePLSphere.exists_original_inward_disk_with_closed_complement
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S T R V : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) {g : E → X}
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (n : κ → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges)
    (hPi : ∀ i, Function.Injective (P i))
    (hPK : ∀ i, (P i).boundary ℝ ⊆ K.space)
    (hdis : Pairwise fun i j => Disjoint (g '' (P i).boundary ℝ) (g '' (P j).boundary ℝ))
    (hR : IsClosed R) (hfront : (⋃ i, g '' (P i).boundary ℝ) = T ∩ frontier R)
    (hST : S ⊆ T) (j : κ) (hPS : g '' (P j).boundary ℝ ⊆ S)
    (hV : IsOpen V) (hrV : g '' (P j).boundary ℝ ⊆ V)
    (hinward : ((g '' (P j).boundary ℝ) ∩ closure (S ∩ interior R)).Nonempty) :
    ∃ (a : ℝ) (f : P2 → X) (E : Set X),
      0 < a ∧ a < 1 ∧ PolyhedralPLInCharts e f D ∧ InjOn f D ∧
      MapsTo f D S ∧ f '' rim = g '' (P j).boundary ℝ ∧ IsClosed E ∧
      (f '' D) ∪ E = S ∧ (f '' D) ∩ E = f '' rim ∧
      f '' {x : P2 | ‖x‖ ∈ Icc a 1} ⊆ V ∧
      f '' {x : P2 | ‖x‖ ∈ Icc a 1} ⊆ R ∧
      (f '' {x : P2 | ‖x‖ ∈ Icc a 1}) \ (f '' rim) ⊆ interior R ∧
      (((g '' (P j).boundary ℝ) ∩ closure (S ∩ Rᶜ)).Nonempty →
        ∀ C : Set X, IsPreconnected C → C ⊆ S → C ⊆ R →
          (C ∩ g '' (P j).boundary ℝ).Nonempty → C ⊆ f '' D) := by
  classical
  let curve := fun i => g '' (P i).boundary ℝ
  have hrclosed (i) : IsClosed (curve i) :=
    ((P i).isCompact_boundary.image_of_continuousOn
      (hg.continuousOn.mono (hPK i))).isClosed
  let O := V ∩ (⋃ i : {i : κ // i ≠ j}, curve i)ᶜ
  have hO : IsOpen O := hV.inter
    (isClosed_iUnion_of_finite (fun i : {i : κ // i ≠ j} => hrclosed i)).isOpen_compl
  have hrO : curve j ⊆ O := by
    intro x hx
    refine ⟨hrV hx,?_⟩
    intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    exact disjoint_left.mp (hdis i.property) hi hx
  have hrfront : curve j ⊆ frontier R := fun x hx =>
    (hfront.subset (mem_iUnion.mpr ⟨j,hx⟩)).2
  have hisolate : (S ∩ O) ∩ frontier R ⊆ curve j := by
    rintro x ⟨⟨hxS,hxO⟩,hxfront⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hfront.symm.subset ⟨hST hxS,hxfront⟩)
    by_cases hij : i = j
    · subst i
      exact hi
    · exact False.elim (hxO.2 (mem_iUnion.mpr ⟨⟨i,hij⟩,hi⟩))
  have hincopy := hinward
  obtain ⟨x,_,hxcl⟩ := hincopy
  obtain ⟨p,hpS,hpR⟩ := (show (closure (S ∩ interior R)).Nonempty from ⟨x,hxcl⟩).of_closure
  have hpnot : p ∉ curve j := fun hp => (hrfront hp).2 hpR
  let J := (P j).simplicialComplex (hP j)
  have hJ := (P j).finite_simplicialComplex_faces (hP j)
  have hJs : J.space = (P j).boundary ℝ := (P j).simplicialComplex_space (hP j)
  have hgP : PolyhedralPLInCharts e g ((P j).boundary ℝ) := by
    rw [←hJs]
    exact hg.restrict_finite J hJ (hJs.subset.trans (hPK j))
  obtain ⟨m,Q,d,_,_,hd,hwhole,hinter,hrim⟩ :=
    s.exists_original_polygon_parameter_cut he (P j) (hP j) (hPi j) hgP
      (hgi.mono (hPK j)) hPS ⟨p,hpS⟩ hpnot
  obtain ⟨a,f,E,ha,ha1,hf,hfi,hfS,hfr,hE,hwhole,hinter,hfO,hfR,hfin,hconfine⟩ :=
    s.exists_inward_disk_with_closed_complement d hd hwhole hinter hR hO
      (by rw [hrim]; exact hrO) (by rw [hrim]; exact hrfront)
      (by rw [hrim]; exact hisolate) (by rw [hrim]; exact hinward)
  refine ⟨a,f,E,ha,ha1,hf,hfi,hfS,hfr.trans hrim,hE,hwhole,hinter,
    hfO.trans inter_subset_left,hfR,hfin,?_⟩
  simpa only [hrim] using hconfine

end PoincareConjecture.M76
