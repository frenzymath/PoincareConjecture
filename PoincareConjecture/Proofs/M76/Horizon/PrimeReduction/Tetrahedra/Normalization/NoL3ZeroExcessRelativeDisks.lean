import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.OriginalZeroExcessDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeInteriorPieces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawCenteredFamilyCollars









set_option autoImplicit false
universe u
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.exists_original_zero_excess_disks_relative_boundary
    {E : Type u} {E' X ι κ ν : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace X] [T2Space X] [Finite κ] [Finite ν]
    {e : ι → OpenPartialHomeomorph X V3} {R Q₀ : Set X} {f : X → E'}
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (B₀ : ν → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hfront : frontier Q₀ = frontier R ∪ ⋃ i, B₀ i)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f (g '' K.space))
    (O : κ → Set X) (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (hQeq : Q₀ = R \ ⋃ i, O i)
    (hO : ∀ i, IsOpen (O i)) (hOR : ∀ i, closure (O i) ⊆ R)
    (hOdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hSC : ∀ i, S i ⊆ closure (O i))
    (hWopen : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hWcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hTR : g '' convexHull ℝ (t : Set E) ⊆ R)
    (hzero : boundaryComponentExcess (⋃ i, S i) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) = 0) :
    ∃ γ : Type u, Finite γ ∧ ∃ cut rim : γ → Set E,
      (∀ j, IsFinitePLBallPair (ℝ × ℝ) (cut j) (rim j)) ∧
      (∀ j, cut j ⊆ convexHull ℝ (t : Set E)) ∧
      (∀ j, cut j ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim j) ∧
      Pairwise (fun j k => Disjoint (cut j) (cut k)) ∧
      g '' (⋃ j, cut j) = (⋃ i, S i) ∩ (g '' convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨HB,c,hc,hci,hc0,_,hopen,hend,hSQ⟩ :=
    exists_signed_collars_of_centered_family S O (fun i => (sS i).isCompact) W
      hQeq hO hOR hOdis hSC hWopen hWcenter
  obtain ⟨γ,hγ,C,hC,hCdis,hCcover,hdisk⟩ :=
    exists_original_boundary_disk_pieces_of_zero_excess he K hK g hg hgi Q A hmap hA
      S sS hS hdis havoid hedges hposition ht ht4 hzero
  let : Finite γ := hγ
  let P := fun j => g '' (C j).space
  have hCK (j) : (C j).space ⊆ K.space := (hC j).2.2.trans (K.convexHull_subset_space ht)
  have hPclosed (j) : IsClosed (P j) :=
    (((C j).isCompact_space_of_finite (hC j).1).image_of_continuousOn
      (hg.continuousOn.mono (hCK j))).isClosed
  have hPconn (j) : IsConnected (P j) := (hC j).2.1.image g (hg.continuousOn.mono (hCK j))
  have hPdis : Pairwise fun j k => Disjoint (P j) (P k) := by
    intro j k hjk
    apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
    exact disjoint_left.mp (hCdis hjk) hx (hgi (hCK k hy) (hCK j hx) hyx ▸ hy)
  have hPcover : (⋃ j, P j) = (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i) := by
    dsimp only [P]
    rw [←image_iUnion,hCcover,image_inter_preimage]
  have hall (j) : IsFinitePLBallPair (ℝ × ℝ) (C j).space
      ((C j).space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) := by
    apply hdisk j
    obtain ⟨x,hx⟩ := (hPconn j).nonempty
    have hxS := hPcover.subset (mem_iUnion.mpr ⟨j,hx⟩)
    have hcc := finite_closed_connected_piece_eq_component P hPclosed hPconn hPdis hPcover j hx
    have hmeet := hno.original_tetrahedral_piece_meets_boundary_relative he K hK g hg hgi S sS hS hdis
      hQ₀ hQ₀PL B₀ sB₀ hB₀dis hfront hf hfi hSQ S HB c (fun _ => 1)
      (fun _ => ⟨zero_lt_one,le_rfl⟩) hc hci hc0 hopen hend ht ht4
      (disjoint_left.mpr (fun _ hxT hxR => hxR.2 (interior_mono hTR hxT))) hxS
    rw [hcc,not_disjoint_iff_nonempty_inter] at hmeet
    obtain ⟨y,hyC,hyF⟩ := hmeet
    obtain ⟨z,hz,hzy⟩ := hyC
    obtain ⟨w,hw,hwy⟩ := hyF
    have hFK : intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ⊆ K.space :=
      (intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans
        (K.convexHull_subset_space ht)
    exact ⟨z,hz,hgi (hFK hw) (hCK j hz) (hwy.trans hzy.symm) ▸ hw⟩
  refine ⟨γ,hγ,(fun j => (C j).space),
    (fun j => (C j).space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))),hall,
    (fun j => (hC j).2.2),(fun _ => rfl),hCdis,?_⟩
  rw [hCcover,image_inter_preimage,inter_comm]

end PoincareConjecture.M76
