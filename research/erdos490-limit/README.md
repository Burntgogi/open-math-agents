# Erdős 490 · 극한 존재의 Lean 증명

곱셈이 A × B에서 단사인 두 집합 A, B ⊆ {1,…,N}에 대해 M(N)을 |A||B|의 최댓값이라 하자. 이 소스는 M(N) log(N) / N²가 유한한 실수로 수렴한다는 명제를 증명한다. 그 실수의 정확한 값은 열려 있다. [공식 명제](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/490.lean#L75)

최종 선언은 `src/Erdos490Limit.lean`의 `Erdos490Verified.limit_exists`다. 공식 선언의 타입을 그대로 받아 독립적인 증명항을 제시한다. 같은 파일의 `transfer`는 환원의 H2를 증명한다. 두 선언 모두 공리 감사에서 `propext`, `Classical.choice`, `Quot.sound`만 사용했다. 첫 실행 기록은 `original-axiom-audit.txt`에 있다.

## 증명의 구조

1. `H1.lean`에서 허용쌍의 정규화한 크기를 임의로 작게 잃으면서 양쪽의 큰 소인수를 분리하고 작은 인수를 유계로 제한한다. `H3.lean`은 이렇게 제한한 쌍들의 균일 상계를 준다.
2. `SeparatedOptimum.lean`에서 각 큰 소인수 부분에 작은 인수들을 어떻게 붙이는지 유한 그래프로 표현한다. `Stability.lean`은 이전 크기들의 부분수열에서 두 소수 집합 중 하나의 정규화된 계수함수가 유계 로그 이동에 안정적임을 보인다.
3. 이전의 큰 소수 p마다 로그축에 질량 1/p인 구간을 잡는다. `BlueStable.lean`은 안정적인 쪽의 곱들을 여러 구간에서 동시에 복구한다. `RedRealization.lean`은 다른 쪽의 곱에 대해 하나의 공통 표본점 x를 고르고, 서로 다른 곱이 중복 집계되지 않음을 이용한다.
4. 이 x를 먼저 고정하면 모든 충분히 큰 새 정수 N에 대해 확대율 log(N)/x를 쓸 수 있다. 이로써 이전 최댓값에 임의로 가깝게 가는 쌍을 모든 큰 N에 만들고, `FinalTransfer.lean`과 공식 환원에서 하극한이 상극한 이상임을 얻는다.

## 재현

Lean 4.33.1, Git, Python 3.10 이상이 필요하다. 아래 명령은 압축을 푼 디렉터리에서 실행한다. 첫 명령은 포함된 모든 소스와 라이선스의 해시를 대조한다.

~~~sh
python replay.py --check-only
git clone https://github.com/google-deepmind/formal-conjectures.git
git -C formal-conjectures checkout 9097e2f90e66d2f6244209cb1c07f7120d17ec53
cd formal-conjectures
lake exe cache get
lake build FormalConjectures/ErdosProblems/490.lean:olean
cd ..
python replay.py formal-conjectures --jobs 2
~~~

검사기는 고정한 formal-conjectures와 Mathlib 커밋 및 Lean 버전을 확인한다. 임시 빌드 디렉터리에서 포함된 소스를 컴파일하고 최종 선언의 공리 목록을 대조한 뒤 `leanchecker`를 실행한다. 중간 모듈을 각각 재생할 때는 마지막 명령에 `--replay-all`을 추가한다.

## 출처

Szemerédi의 크기 상계, Erdős와 Szemerédi의 소인수 분리 논법, van Doorn의 구성 및 소수 집합에 대한 관찰을 선행 결과로 사용했다. [Erdős 490의 문헌과 토론](https://www.erdosproblems.com/490)

분석 입력은 PrimeNumberTheoremAnd의 강한 소수정리와 Mertens 정리다. 해당 증명에서 가져오는 LeanArchitect 소스도 포함되어 있다. 두 프로젝트의 소스 저작권 표시와 Apache 2.0 라이선스를 보존했다. 모듈별 해시와 고정 리비전은 `manifest.json`에 있다. [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/3853b4ba456ebf0d441e46c68df49231b5ec0d8a) · [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect/tree/0f5bc0209ae02a7fb0cfe7d113d4094542cee221)
