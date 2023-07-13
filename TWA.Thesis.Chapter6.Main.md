<pre class="Agda"><a id="9" class="Symbol">{-#</a> <a id="13" class="Keyword">OPTIONS</a> <a id="21" class="Pragma">--without-K</a> <a id="33" class="Pragma">--exact-split</a> <a id="47" class="Symbol">#-}</a>

<a id="52" class="Keyword">open</a> <a id="57" class="Keyword">import</a> <a id="64" href="UF.FunExt.html" class="Module">UF.FunExt</a>
<a id="74" class="Keyword">open</a> <a id="79" class="Keyword">import</a> <a id="86" href="UF.Subsingletons.html" class="Module">UF.Subsingletons</a>
<a id="103" class="Keyword">open</a> <a id="108" class="Keyword">import</a> <a id="115" href="Integers.Type.html" class="Module">Integers.Type</a>
<a id="129" class="Keyword">open</a> <a id="134" class="Keyword">import</a> <a id="141" href="MLTT.Spartan.html" class="Module">MLTT.Spartan</a>
<a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="Unsafe.Haskell.html" class="Module">Unsafe.Haskell</a>
<a id="181" class="Keyword">open</a> <a id="186" class="Keyword">import</a> <a id="193" href="TWA.Thesis.Chapter5.SignedDigit.html" class="Module">TWA.Thesis.Chapter5.SignedDigit</a>
<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="TWA.Thesis.Chapter2.Vectors.html" class="Module">TWA.Thesis.Chapter2.Vectors</a> <a id="265" class="Keyword">hiding</a> <a id="272" class="Symbol">(</a><a id="273" href="TWA.Thesis.Chapter2.Vectors.html#3085" class="Function Operator">_+++_</a><a id="278" class="Symbol">)</a>

<a id="281" class="Keyword">module</a> <a id="288" href="TWA.Thesis.Chapter6.Main.html" class="Module">TWA.Thesis.Chapter6.Main</a> <a id="313" class="Keyword">where</a>

<a id="320" class="Keyword">postulate</a> <a id="fe"></a><a id="330" href="TWA.Thesis.Chapter6.Main.html#330" class="Postulate">fe</a> <a id="333" class="Symbol">:</a> <a id="335" href="UF.FunExt.html#970" class="Function">FunExt</a>
<a id="342" class="Keyword">postulate</a> <a id="pe"></a><a id="352" href="TWA.Thesis.Chapter6.Main.html#352" class="Postulate">pe</a> <a id="355" class="Symbol">:</a> <a id="357" href="UF.Subsingletons.html#14254" class="Function">PropExt</a>

<a id="366" class="Keyword">open</a> <a id="371" class="Keyword">import</a> <a id="378" href="TWA.Thesis.Chapter6.SignedDigitExamples.html" class="Module">TWA.Thesis.Chapter6.SignedDigitExamples</a> <a id="418" href="TWA.Thesis.Chapter6.Main.html#330" class="Postulate">fe</a> <a id="421" href="TWA.Thesis.Chapter6.Main.html#352" class="Postulate">pe</a>

<a id="𝟚ᴺ"></a><a id="425" href="TWA.Thesis.Chapter6.Main.html#425" class="Function">𝟚ᴺ</a> <a id="428" class="Symbol">=</a> <a id="430" href="MLTT.Natural-Numbers-Type.html#110" class="Datatype">ℕ</a> <a id="432" class="Symbol">→</a> <a id="434" href="MLTT.Two.html#138" class="Datatype">𝟚</a>

<a id="𝟛-to-ℤ"></a><a id="437" href="TWA.Thesis.Chapter6.Main.html#437" class="Function">𝟛-to-ℤ</a> <a id="444" class="Symbol">:</a> <a id="446" href="TWA.Thesis.Chapter5.SignedDigit.html#313" class="Datatype">𝟛</a> <a id="448" class="Symbol">→</a> <a id="450" href="Integers.Type.html#776" class="Datatype">ℤ</a>
<a id="452" href="TWA.Thesis.Chapter6.Main.html#437" class="Function">𝟛-to-ℤ</a> <a id="459" href="TWA.Thesis.Chapter5.SignedDigit.html#330" class="InductiveConstructor">−1</a> <a id="462" class="Symbol">=</a> <a id="464" href="Integers.Type.html#809" class="InductiveConstructor">negsucc</a> <a id="472" class="Number">0</a>
<a id="474" href="TWA.Thesis.Chapter6.Main.html#437" class="Function">𝟛-to-ℤ</a>  <a id="482" href="TWA.Thesis.Chapter5.SignedDigit.html#333" class="InductiveConstructor">O</a> <a id="484" class="Symbol">=</a> <a id="486" href="Integers.Type.html#792" class="InductiveConstructor">pos</a> <a id="490" class="Number">0</a>
<a id="492" href="TWA.Thesis.Chapter6.Main.html#437" class="Function">𝟛-to-ℤ</a> <a id="499" href="TWA.Thesis.Chapter5.SignedDigit.html#335" class="InductiveConstructor">+1</a> <a id="502" class="Symbol">=</a> <a id="504" href="Integers.Type.html#792" class="InductiveConstructor">pos</a> <a id="508" class="Number">1</a>

<a id="show𝟛"></a><a id="511" href="TWA.Thesis.Chapter6.Main.html#511" class="Function">show𝟛</a> <a id="517" class="Symbol">:</a> <a id="519" href="TWA.Thesis.Chapter5.SignedDigit.html#313" class="Datatype">𝟛</a> <a id="521" class="Symbol">→</a> <a id="523" href="Unsafe.Haskell.html#362" class="Postulate">String</a>
<a id="530" href="TWA.Thesis.Chapter6.Main.html#511" class="Function">show𝟛</a> <a id="536" class="Symbol">=</a> <a id="538" href="Unsafe.Haskell.html#1693" class="Function">showℤ</a> <a id="544" href="MLTT.Pi.html#527" class="Function Operator">∘</a> <a id="546" href="TWA.Thesis.Chapter6.Main.html#437" class="Function">𝟛-to-ℤ</a>

<a id="show𝟚ᴺ-prefix"></a><a id="554" href="TWA.Thesis.Chapter6.Main.html#554" class="Function">show𝟚ᴺ-prefix</a> <a id="568" class="Symbol">:</a> <a id="570" class="Symbol">(</a><a id="571" href="MLTT.Natural-Numbers-Type.html#110" class="Datatype">ℕ</a> <a id="573" class="Symbol">→</a> <a id="575" href="MLTT.Two.html#138" class="Datatype">𝟚</a><a id="576" class="Symbol">)</a> <a id="578" class="Symbol">→</a> <a id="580" href="MLTT.Natural-Numbers-Type.html#110" class="Datatype">ℕ</a> <a id="582" class="Symbol">→</a> <a id="584" href="Unsafe.Haskell.html#362" class="Postulate">String</a>
<a id="591" href="TWA.Thesis.Chapter6.Main.html#554" class="Function">show𝟚ᴺ-prefix</a> <a id="605" href="TWA.Thesis.Chapter6.Main.html#605" class="Bound">x</a> <a id="607" class="Number">0</a> <a id="609" class="Symbol">=</a> <a id="611" class="String">&quot;&quot;</a>
<a id="614" href="TWA.Thesis.Chapter6.Main.html#554" class="Function">show𝟚ᴺ-prefix</a> <a id="628" href="TWA.Thesis.Chapter6.Main.html#628" class="Bound">x</a> <a id="630" class="Symbol">(</a><a id="631" href="MLTT.Natural-Numbers-Type.html#137" class="InductiveConstructor">succ</a> <a id="636" href="TWA.Thesis.Chapter6.Main.html#636" class="Bound">n</a><a id="637" class="Symbol">)</a>
 <a id="640" class="Symbol">=</a> <a id="642" href="TWA.Thesis.Chapter6.Main.html#511" class="Function">show𝟛</a> <a id="648" class="Symbol">(</a><a id="649" href="TWA.Thesis.Chapter6.SignedDigitExamples.html#1337" class="Function">𝟚→𝟛</a> <a id="653" class="Symbol">(</a><a id="654" href="TWA.Thesis.Chapter6.Main.html#628" class="Bound">x</a> <a id="656" class="Number">0</a><a id="657" class="Symbol">))</a> <a id="660" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="664" class="String">&quot;,&quot;</a> <a id="668" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="672" href="TWA.Thesis.Chapter6.Main.html#554" class="Function">show𝟚ᴺ-prefix</a> <a id="686" class="Symbol">(</a><a id="687" href="TWA.Thesis.Chapter6.Main.html#628" class="Bound">x</a> <a id="689" href="MLTT.Pi.html#527" class="Function Operator">∘</a> <a id="691" href="MLTT.Natural-Numbers-Type.html#137" class="InductiveConstructor">succ</a><a id="695" class="Symbol">)</a> <a id="697" href="TWA.Thesis.Chapter6.Main.html#636" class="Bound">n</a>

<a id="show𝟛ᴺ-prefix"></a><a id="700" href="TWA.Thesis.Chapter6.Main.html#700" class="Function">show𝟛ᴺ-prefix</a> <a id="714" class="Symbol">:</a> <a id="716" href="TWA.Thesis.Chapter5.SignedDigit.html#1150" class="Function">𝟛ᴺ</a> <a id="719" class="Symbol">→</a> <a id="721" href="MLTT.Natural-Numbers-Type.html#110" class="Datatype">ℕ</a> <a id="723" class="Symbol">→</a> <a id="725" href="Unsafe.Haskell.html#362" class="Postulate">String</a>
<a id="732" href="TWA.Thesis.Chapter6.Main.html#700" class="Function">show𝟛ᴺ-prefix</a> <a id="746" href="TWA.Thesis.Chapter6.Main.html#746" class="Bound">x</a> <a id="748" class="Number">0</a> <a id="750" class="Symbol">=</a> <a id="752" class="String">&quot;&quot;</a>
<a id="755" href="TWA.Thesis.Chapter6.Main.html#700" class="Function">show𝟛ᴺ-prefix</a> <a id="769" href="TWA.Thesis.Chapter6.Main.html#769" class="Bound">x</a> <a id="771" class="Symbol">(</a><a id="772" href="MLTT.Natural-Numbers-Type.html#137" class="InductiveConstructor">succ</a> <a id="777" href="TWA.Thesis.Chapter6.Main.html#777" class="Bound">n</a><a id="778" class="Symbol">)</a>
 <a id="781" class="Symbol">=</a> <a id="783" href="TWA.Thesis.Chapter6.Main.html#511" class="Function">show𝟛</a> <a id="789" class="Symbol">(</a><a id="790" href="TWA.Thesis.Chapter6.Main.html#769" class="Bound">x</a> <a id="792" class="Number">0</a><a id="793" class="Symbol">)</a> <a id="795" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="799" class="String">&quot;,&quot;</a> <a id="803" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="807" href="TWA.Thesis.Chapter6.Main.html#700" class="Function">show𝟛ᴺ-prefix</a> <a id="821" class="Symbol">(</a><a id="822" href="TWA.Thesis.Chapter6.Main.html#769" class="Bound">x</a> <a id="824" href="MLTT.Pi.html#527" class="Function Operator">∘</a> <a id="826" href="MLTT.Natural-Numbers-Type.html#137" class="InductiveConstructor">succ</a><a id="830" class="Symbol">)</a> <a id="832" href="TWA.Thesis.Chapter6.Main.html#777" class="Bound">n</a>

<a id="show𝟛ᴺ×𝟛ᴺ-prefix"></a><a id="835" href="TWA.Thesis.Chapter6.Main.html#835" class="Function">show𝟛ᴺ×𝟛ᴺ-prefix</a> <a id="852" class="Symbol">:</a> <a id="854" href="TWA.Thesis.Chapter5.SignedDigit.html#1150" class="Function">𝟛ᴺ</a> <a id="857" href="MLTT.Sigma.html#572" class="Function Operator">×</a> <a id="859" href="TWA.Thesis.Chapter5.SignedDigit.html#1150" class="Function">𝟛ᴺ</a> <a id="862" class="Symbol">→</a> <a id="864" href="MLTT.Natural-Numbers-Type.html#110" class="Datatype">ℕ</a> <a id="866" class="Symbol">→</a> <a id="868" href="Unsafe.Haskell.html#362" class="Postulate">String</a>
<a id="875" href="TWA.Thesis.Chapter6.Main.html#835" class="Function">show𝟛ᴺ×𝟛ᴺ-prefix</a> <a id="892" class="Symbol">(</a><a id="893" href="TWA.Thesis.Chapter6.Main.html#893" class="Bound">x</a> <a id="895" href="MLTT.Sigma.html#409" class="InductiveConstructor Operator">,</a> <a id="897" href="TWA.Thesis.Chapter6.Main.html#897" class="Bound">y</a><a id="898" class="Symbol">)</a> <a id="900" href="TWA.Thesis.Chapter6.Main.html#900" class="Bound">n</a>
 <a id="903" class="Symbol">=</a> <a id="905" href="TWA.Thesis.Chapter6.Main.html#700" class="Function">show𝟛ᴺ-prefix</a> <a id="919" href="TWA.Thesis.Chapter6.Main.html#893" class="Bound">x</a> <a id="921" href="TWA.Thesis.Chapter6.Main.html#900" class="Bound">n</a> <a id="923" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="927" class="String">&quot; ;\n&quot;</a> <a id="934" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="938" href="TWA.Thesis.Chapter6.Main.html#700" class="Function">show𝟛ᴺ-prefix</a> <a id="952" href="TWA.Thesis.Chapter6.Main.html#897" class="Bound">y</a> <a id="954" href="TWA.Thesis.Chapter6.Main.html#900" class="Bound">n</a>

<a id="show𝟚ᴺ×𝟚ᴺ-prefix"></a><a id="957" href="TWA.Thesis.Chapter6.Main.html#957" class="Function">show𝟚ᴺ×𝟚ᴺ-prefix</a> <a id="974" class="Symbol">:</a> <a id="976" href="TWA.Thesis.Chapter6.Main.html#425" class="Function">𝟚ᴺ</a> <a id="979" href="MLTT.Sigma.html#572" class="Function Operator">×</a> <a id="981" href="TWA.Thesis.Chapter6.Main.html#425" class="Function">𝟚ᴺ</a> <a id="984" class="Symbol">→</a> <a id="986" href="MLTT.Natural-Numbers-Type.html#110" class="Datatype">ℕ</a> <a id="988" class="Symbol">→</a> <a id="990" href="Unsafe.Haskell.html#362" class="Postulate">String</a>
<a id="997" href="TWA.Thesis.Chapter6.Main.html#957" class="Function">show𝟚ᴺ×𝟚ᴺ-prefix</a> <a id="1014" class="Symbol">(</a><a id="1015" href="TWA.Thesis.Chapter6.Main.html#1015" class="Bound">x</a> <a id="1017" href="MLTT.Sigma.html#409" class="InductiveConstructor Operator">,</a> <a id="1019" href="TWA.Thesis.Chapter6.Main.html#1019" class="Bound">y</a><a id="1020" class="Symbol">)</a> <a id="1022" href="TWA.Thesis.Chapter6.Main.html#1022" class="Bound">n</a>
 <a id="1025" class="Symbol">=</a> <a id="1027" href="TWA.Thesis.Chapter6.Main.html#554" class="Function">show𝟚ᴺ-prefix</a> <a id="1041" href="TWA.Thesis.Chapter6.Main.html#1015" class="Bound">x</a> <a id="1043" href="TWA.Thesis.Chapter6.Main.html#1022" class="Bound">n</a> <a id="1045" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="1049" class="String">&quot; ;\n&quot;</a> <a id="1056" href="Unsafe.Haskell.html#1777" class="Function Operator">+++</a> <a id="1060" href="TWA.Thesis.Chapter6.Main.html#554" class="Function">show𝟚ᴺ-prefix</a> <a id="1074" href="TWA.Thesis.Chapter6.Main.html#1019" class="Bound">y</a> <a id="1076" href="TWA.Thesis.Chapter6.Main.html#1022" class="Bound">n</a>


<a id="1080" class="Keyword">open</a> <a id="1085" href="TWA.Thesis.Chapter6.SignedDigitExamples.html#13926" class="Module">Regression-Example1a</a>

<a id="main"></a><a id="1107" href="TWA.Thesis.Chapter6.Main.html#1107" class="Function">main</a> <a id="1112" class="Symbol">:</a> <a id="1114" href="Unsafe.Haskell.html#1233" class="Postulate">IO</a> <a id="1117" href="Unsafe.Haskell.html#1397" class="Record">Unit</a>
<a id="1122" href="TWA.Thesis.Chapter6.Main.html#1107" class="Function">main</a> <a id="1127" class="Symbol">=</a> <a id="1129" href="Unsafe.Haskell.html#1520" class="Postulate">putStrLn</a> <a id="1138" class="Symbol">(</a><a id="1139" href="TWA.Thesis.Chapter6.Main.html#554" class="Function">show𝟚ᴺ-prefix</a> <a id="1153" class="Symbol">(</a><a id="1154" href="TWA.Thesis.Chapter6.SignedDigitExamples.html#13826" class="Function">opt𝓞</a> <a id="1159" class="Number">12</a><a id="1161" class="Symbol">)</a> <a id="1163" class="Number">30</a>
     <a id="1171" class="Comment">--       +++ &quot;\n&quot; +++ show𝟚ᴺ-prefix (example&#39; 2) 30</a>
       <a id="1230" class="Comment">--   +++ &quot;\n&quot; +++ show𝟚ᴺ-prefix (example&#39; 3) 30</a>
         <a id="1287" class="Comment">-- +++ &quot;\n&quot; +++ show𝟚ᴺ-prefix (example&#39; 4) 30</a>
       <a id="1340" class="Comment">--   +++ &quot;\n&quot; +++ show𝟚ᴺ-prefix (example&#39; 5) 30</a>
           <a id="1399" class="Symbol">)</a>
            <a id="1413" class="Comment">--  ++ show𝟚ᴺ-prefix (example2 </a>



<a id="1448" class="Comment">-- putStrLn (show𝟛ᴺ-prefix (preg-test-eq fe 6 (1/3 fe)) 50)</a>

</pre>
Optimisation example 1 : Minimise neg to 8 degrees of precision
More complex examples get stack overflow or take too long :(

Search example 1 : Find x such that (-x/2) ≼ⁿ 1/4 (precisions 0,1,5,50,etc)
Search example 2 : Find x : ℕ → X such that x = bigMid O

For regression examples: first apply the regressed function
                         to points [-1, -2/3, -1/3, O, 1/3, 2/3, 1]
                         then check the parameters

Regression example 1  : Regress id using model (λ y x → neg y ⊕ x)
 [Global opt]
 
Regression example 2' : Regress (λ x → 1/3 ⊕ x) using the model (λ y x → y ⊕ x)
                        and pseudocloseness function from points [-1,O,1]
                        Precision level 8 worked well
 [Perfect]
Regression example 2  : Regress (λ x → 1/3 ⊕ x²) using the model (λ y x → y ⊕ x²)
                        and pseudocloseness function from points [-1,O,1]

Regression example 3  : Line of best fit the points (-1,-1), (O,O), (1,-1)
 [Interpolated]

Regression example 4  : 