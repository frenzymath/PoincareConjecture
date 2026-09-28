import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalActualCutBallPrism
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalFaceChartFamily









set_option autoImplicit false
universe v
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "V3" => (Fin 3 → ℝ)
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_global_original_prism_family
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1) :
    ∃ G : ∀ s k, Square ≃ₜ (D s).carrier k,
      (∀ s k, (G s k).IsFinitePL) ∧
      (∀ s k x, (G s k x : E) ∈ (D s).arc ((D s).cap k false) ↔
        (x : ℝ × ℝ).2 = 0) ∧
      (∀ s k x, (G s k x : E) ∈ (D s).arc ((D s).cap k true) ↔
        (x : ℝ × ℝ).2 = 1) ∧
      (∀ s k b x, (G s k x : E) ∈ (D s).side k b ↔
        (x : ℝ × ℝ).1 = if b then 1 else 0) ∧
      (∀ s k b t, (G s k (sidePoint b t) : E) =
        AffineMap.lineMap (G s k (sidePoint b 0) : E)
          (G s k (sidePoint b 1) : E) (t : ℝ)) ∧
      ∀ (ι : Type v) [Finite ι] [DecidableEq ι],
      ∀ {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4),
      let Dₜ := fun f : TetrahedronFace K t => D f.1
      ∀
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hsub : ∀ i, cut i ⊆ convexHull ℝ (t : Set E))
    (hrim : ∀ i, cut i ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim i)
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E)))
    {B R : Set E} (hB : IsFinitePLBallPair V3 B R)
    (hR : R = B ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i))
    (hwhole : ∀ i, (B ∩ cut i).Nonempty → cut i ⊆ R)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (Dₜ f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (Dₜ f).exceptional),
    ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ cut i₀ ⊆ R ∧ cut i₁ ⊆ R ∧
      ∃ flip : CutBallRectangle Dₜ B → Bool,
      ∃ H : (cut i₀ ×ˢ I : Set (E × ℝ)) ≃ₜ B, H.IsFinitePL ∧
        (∀ (x : E) (hx : x ∈ cut i₀), (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
        (∀ x, (H x : E) ∈ cut i₀ ↔ (x : E × ℝ).2 = 0) ∧
        (∀ x, (H x : E) ∈ cut i₁ ↔ (x : E × ℝ).2 = 1) ∧
        (∀ z x, (H x : E) ∈ (Dₜ z.1.1).carrier z.1.2 ↔
          (x : E × ℝ).1 ∈ (Dₜ z.1.1).arc ((Dₜ z.1.1).cap z.1.2 (flip z))) ∧
        ∀ (z : CutBallRectangle Dₜ B) (u t : I),
          (H.symm ⟨G z.1.1.1 z.1.2 ⟨(u,fiberFlip (flip z) t),u.property,(fiberFlip (flip z) t).property⟩,
            z.2 (G z.1.1.1 z.1.2 _).property⟩ : E × ℝ) =
            ((G z.1.1.1 z.1.2 ⟨(u,fiberFlip (flip z) 0),u.property,(fiberFlip (flip z) 0).property⟩ : E),(t : ℝ)) := by
  obtain ⟨G,hG,hW,hZ,hL,hside⟩ := exists_global_face_chart_family D
  refine ⟨G,hG,hW,hZ,hL,hside,?_⟩
  intro ι hι hdec t ht ht4
  dsimp only
  intro cut rim hcut hsub hrim hdis hphysical B R hB hR hwhole hcomp hregular
  exact exists_actual_global_cut_ball_prism K hK g hgi ht ht4
    (fun f => D f.1) cut rim hcut hsub hrim hdis hphysical hB hR hwhole hcomp hregular
    (fun z => G z.1.1.1 z.1.2) (fun z => hG _ _)
    (fun z => hW _ _) (fun z => hZ _ _) (fun z => hL _ _) (fun z => hside _ _)

end PoincareConjecture.M76.PrismBelt
