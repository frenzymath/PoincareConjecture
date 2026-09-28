import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalSurfacePieces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.FiniteDiskBallDecomposition









set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_disk_piece_complement
    {E : Type u} {X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    ∃ γ : Type u, Finite γ ∧ ∃ C : γ → SimplicialComplex ℝ E,
      (∀ c, (C c).faces.Finite ∧ IsConnected (C c).space ∧
        (C c).space ⊆ convexHull ℝ (t : Set E)) ∧
      Pairwise (fun c d => Disjoint (C c).space (C d).space) ∧
      (⋃ c, (C c).space) = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) ∧
      ∃ β : Type, Finite β ∧ ∃ B R : β → Set E,
        let Q := intrinsicFrontier ℝ (convexHull ℝ (t : Set E))
        let disk := fun c => IsFinitePLBallPair (ℝ × ℝ) (C c).space ((C c).space ∩ Q)
        let cuts := ⋃ c : {c : γ // disk c}, (C c).space
        Nat.card β = Nat.card {c : γ // disk c} + 1 ∧
        (∀ b, IsFinitePLBallPair V3 (B b) (R b)) ∧
        (∀ b, R b = B b ∩ (Q ∪ cuts)) ∧
        (⋃ b, B b) = convexHull ℝ (t : Set E) ∧
        Pairwise (fun b d => B b ∩ B d ⊆ cuts) ∧
        ∀ c, ¬ disk c → ∃! b, (C c).space ⊆ B b ∧
          (C c).space ∩ R b = (C c).space ∩ Q := by
  classical
  obtain ⟨γ,hγ,C,P,hC,hCdis,_,hcover,_,_,_⟩ :=
    exists_original_sphere_pieces_in_face he K hK g hg hgi S sS hS hdis ht
  let : Finite γ := hγ
  let Q := intrinsicFrontier ℝ (convexHull ℝ (t : Set E))
  let disk := fun c => IsFinitePLBallPair (ℝ × ℝ) (C c).space ((C c).space ∩ Q)
  let D := {c : γ // disk c}
  let cuts := ⋃ c : D, (C c).space
  have hball := isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4
  obtain ⟨β,hβ,B,R,hcard,hB,hR,hBcover,hinter⟩ :=
    exists_finite_proper_disk_ball_decomposition hball
      (fun c : D => (C c).space) (fun c : D => (C c).space ∩ Q)
      (fun c => c.property) (fun c => (hC c).2.2.1) (fun _ => rfl)
      (fun c d hcd => hCdis (fun heq => hcd (Subtype.ext heq)))
  let : Finite β := hβ
  refine ⟨γ,hγ,C,fun c => ⟨(hC c).1,(hC c).2.1,(hC c).2.2.1⟩,
    hCdis,hcover,β,hβ,B,R,hcard,hB,hR,hBcover,hinter,?_⟩
  intro c hnot
  have hmiss : Disjoint (C c).space cuts := by
    apply disjoint_left.mpr
    intro x hxc hxt
    obtain ⟨d,hxd⟩ := mem_iUnion.mp hxt
    have hcd : c ≠ d := fun heq => hnot (heq ▸ d.property)
    exact disjoint_left.mp (hCdis hcd) hxc hxd
  obtain ⟨b,hcb,hunique⟩ := exists_unique_disk_owner_away_from_cuts B
    (fun b => (hB b).isCompact.isClosed) hBcover hinter
    (hC c).2.1 (hC c).2.2.1 hmiss
  refine ⟨b,⟨hcb,?_⟩,fun d hd => hunique d hd.1⟩
  rw [hR b]
  ext x
  constructor
  · rintro ⟨hxc,_,hxQ | hxcut⟩
    · exact ⟨hxc,hxQ⟩
    · exact (disjoint_left.mp hmiss hxc hxcut).elim
  · rintro ⟨hxc,hxQ⟩
    exact ⟨hxc,hcb hxc,Or.inl hxQ⟩

end PoincareConjecture.M76
