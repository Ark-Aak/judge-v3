import { TestData, SubtaskScoringType, TestcaseJudge } from '../interfaces';
import { CompilationResult, JudgeResult, TaskStatus, SubtaskResult, TestcaseDetails } from '../../interfaces';
import { Language } from '../../languages';
import { compile } from './compile';
import winston = require('winston');
import _ = require('lodash');

const globalFullScore = 100;
function calculateSubtaskScore(scoring: SubtaskScoringType, scores: number[]): number {
    if (scoring === SubtaskScoringType.Minimum) {
        return _.min(scores);
    } else if (scoring === SubtaskScoringType.Multiple) {
        return _.reduce(scores,
            (res, cur) => res * cur, 1);
    } else if (scoring === SubtaskScoringType.Summation) {
        return _.sum(scores) / scores.length;
    }
}


class vex {
    data: any;
    firstEdge: adjvex;
    in: number;

    constructor(value) {
        this.data = value;
        this.firstEdge = null;
        this.in = 0;
    }

}

class adjvex {
    node: any;
    next: adjvex;

    constructor(node) {
        this.node = node;
        this.next = null;
    }
}

class Graph {
    adjList: vex[];

    constructor(v, vr) {
        let len = v.length;
        let vexs = new Array(len);
        let v1 = 0, v2 = 0;
        let newvex = null;
        for (let i = 0; i < len; i++) {
            vexs[i] = new vex(v[i]);
        }
        for (let arc of vr) {
            v1 = v.indexOf(arc[0]);
            v2 = v.indexOf(arc[1]);
            newvex = new adjvex(v2);
            newvex.next = vexs[v1].firstEdge;
            vexs[v1].firstEdge = newvex;
            vexs[v2].in++;
        }
        this.adjList = vexs;
    }
}

function topoSort(G: Graph) {
    let stack = [];
    for (let i = 0; i < G.adjList.length; i++) {
        if (G.adjList[i].in === 0) {
            stack.push(i);
        }
    }

    let currentVex = null;
    let count = 0;
    let res = [];
    while (stack.length > 0) {
        currentVex = G.adjList[stack.pop()];
        res.push(currentVex.data);
        count++;
        currentVex = currentVex.firstEdge;
        while (currentVex) {
            if ((--G.adjList[currentVex.node].in) === 0) {
                stack.push(currentVex.node);
            }
            currentVex = currentVex.next;
        }
    }
    return res;
}

export abstract class JudgerBase {
    priority: number;
    testData: TestData;

    constructor(t: TestData, p: number) {
        this.priority = p;
        this.testData = t;
    }

    async preprocessTestData(): Promise<void> { }

    abstract compile(): Promise<CompilationResult>;

    async judge(reportProgressResult: (p: JudgeResult) => Promise<void>): Promise<JudgeResult> {
        const results: SubtaskResult[] = this.testData.subtasks.map(t => ({
            cases: t.cases.map(j => ({
                status: TaskStatus.Waiting,
                result: { scoringRate: t.type !== SubtaskScoringType.Summation ? 1 : 0 } as any
            })),
            status: TaskStatus.Waiting
        }));

        const updateSubtaskScore = (currentTask, currentResult) => {
            if (currentResult.cases.some(c => c.status === TaskStatus.Failed)) {
                // If any testcase has failed, the score is invaild.
                currentResult.score = NaN;
            } else {
                currentResult.score = calculateSubtaskScore(currentTask.type, currentResult.cases.map(c => c.result ? c.result.scoringRate : 0)) * currentTask.score;
            }
        }

        const testcaseDetailsCache: Map<string, TestcaseDetails> = new Map();
        const judgeTestcaseWrapper = async (curCase: TestcaseJudge, started: () => Promise<void>): Promise<TestcaseDetails> => {
            if (testcaseDetailsCache.has(curCase.name)) {
                return testcaseDetailsCache.get(curCase.name);
            }

            const result: TestcaseDetails = await this.judgeTestcase(curCase, started);
            testcaseDetailsCache.set(curCase.name, result);

            return result;
        }

        for (let subtaskIndex = 0; subtaskIndex < this.testData.subtasks.length; subtaskIndex++) {
            const currentResult = results[subtaskIndex];
            const currentTask = this.testData.subtasks[subtaskIndex];
            updateSubtaskScore(currentTask, currentResult);
        }

        const reportProgress = function () {
            reportProgressResult({ subtasks: results });
        }
        winston.debug(`Totally ${results.length} subtasks.`);
        let hasDependencies = false;
        const judgeTasks: Promise<void>[] = [];
        let indexs = [], edges = [];
        for (let subtaskIndex = 0; subtaskIndex < this.testData.subtasks.length; subtaskIndex++) {
            indexs.push(subtaskIndex);
            if (this.testData.subtasks[subtaskIndex].dependencies !== undefined && this.testData.subtasks[subtaskIndex].dependencies.length > 0) {
                this.testData.subtasks[subtaskIndex].dependencies.forEach((dep) => {
                    edges.push([dep - 1, subtaskIndex]);
                    hasDependencies = true;
                });
            }
        }
        let graph = new Graph(indexs, edges);
        let order = topoSort(graph);
        const validDAG = (order.length === this.testData.subtasks.length);
        for (let i = 0; i < this.testData.subtasks.length; i++) {
            let flg = false;
            for (let j = 0; j < order.length; j++) {
                if (order[j] === i) {
                    flg = true;
                    break;
                }
            }
            if (!flg) {
                order.push(i);
            }
        }
        if (!hasDependencies) {
            for (let subtaskIndex = 0; subtaskIndex < this.testData.subtasks.length; subtaskIndex++) {
                const currentResult = results[subtaskIndex];
                const currentTask = this.testData.subtasks[subtaskIndex];

                const updateCurrentSubtaskScore = () => updateSubtaskScore(currentTask, currentResult);

                judgeTasks.push((async () => {
                    // Type minimum is skippable, run one by one
                    if (currentTask.type !== SubtaskScoringType.Summation) {
                        let skipped: boolean = false;
                        for (let index = 0; index < currentTask.cases.length; index++) {
                            const currentTaskResult = currentResult.cases[index];
                            if (skipped) {
                                currentTaskResult.status = TaskStatus.Skipped;
                            } else {
                                winston.verbose(`Judging ${subtaskIndex}, case ${index}.`);
                                let score = 0;
                                try {
                                    const taskJudge = await judgeTestcaseWrapper(currentTask.cases[index], async () => {
                                        currentTaskResult.status = TaskStatus.Running;
                                        await reportProgress();
                                    });
                                    currentTaskResult.status = TaskStatus.Done;
                                    currentTaskResult.result = taskJudge;
                                    score = taskJudge.scoringRate;
                                } catch (err) {
                                    currentTaskResult.status = TaskStatus.Failed;
                                    currentTaskResult.errorMessage = err.toString();
                                    winston.warn(`Task runner error: ${err.toString()} (subtask ${subtaskIndex}, case ${index})`);
                                }
                                if (score == null || isNaN(score) || score === 0) {
                                    winston.debug(`Subtask ${subtaskIndex}, case ${index}: zero, skipping the rest.`);
                                    skipped = true;
                                }
                                updateCurrentSubtaskScore();
                                await reportProgress();
                            }
                        }
                    } else {
                        // Non skippable, run all immediately
                        const caseTasks: Promise<void>[] = [];
                        for (let index = 0; index < currentTask.cases.length; index++) {
                            caseTasks.push((async () => {
                                const currentTaskResult = currentResult.cases[index];
                                winston.verbose(`Judging ${subtaskIndex}, case ${index}.`);
                                try {
                                    currentTaskResult.result = await judgeTestcaseWrapper(currentTask.cases[index], async () => {
                                        currentTaskResult.status = TaskStatus.Running;
                                        await reportProgress();
                                    });
                                    currentTaskResult.status = TaskStatus.Done;
                                } catch (err) {
                                    currentTaskResult.status = TaskStatus.Failed;
                                    currentTaskResult.errorMessage = err.toString();
                                    winston.warn(`Task runner error: ${err.toString()} (subtask ${subtaskIndex}, case ${index})`);
                                }
                                updateCurrentSubtaskScore();
                                await reportProgress();
                            })());
                        }
                        await Promise.all(caseTasks);
                    }
                    updateCurrentSubtaskScore();
                    winston.verbose(`Subtask ${subtaskIndex}, finished`);
                })());
            }
            await Promise.all(judgeTasks);
            return { subtasks: results };
        }
        else {
            for (let subtaskIndexO = 0; subtaskIndexO < order.length; subtaskIndexO++) {
                let subtaskIndex = order[subtaskIndexO];
                const currentResult = results[subtaskIndex];
                const currentTask = this.testData.subtasks[subtaskIndex];

                const updateCurrentSubtaskScore = () => updateSubtaskScore(currentTask, currentResult);

                let validDep = true;

                if (currentTask.dependencies !== undefined && currentTask.dependencies.length > 0) {
                    for (let dep of currentTask.dependencies) {
                        let rdep = dep - 1;
                        if (results[rdep].score !== this.testData.subtasks[rdep].score) {
                            validDep = false;
                        }
                    }
                }

                // Type minimum is skippable, run one by one
                if (currentTask.type !== SubtaskScoringType.Summation) {
                    let skipped: boolean = false;
                    for (let index = 0; index < currentTask.cases.length; index++) {
                        const currentTaskResult = currentResult.cases[index];
                        if (skipped || !validDAG || !validDep) {
                            currentTaskResult.status = TaskStatus.Skipped;
                            currentTaskResult.result.scoringRate = 0;
                        } else {
                            winston.verbose(`Judging ${subtaskIndex}, case ${index}.`);
                            let score = 0;
                            try {
                                const taskJudge = await judgeTestcaseWrapper(currentTask.cases[index], async () => {
                                    currentTaskResult.status = TaskStatus.Running;
                                    await reportProgress();
                                });
                                currentTaskResult.status = TaskStatus.Done;
                                currentTaskResult.result = taskJudge;
                                score = taskJudge.scoringRate;
                            } catch (err) {
                                currentTaskResult.status = TaskStatus.Failed;
                                currentTaskResult.errorMessage = err.toString();
                                winston.warn(`Task runner error: ${err.toString()} (subtask ${subtaskIndex}, case ${index})`);
                            }
                            if (score == null || isNaN(score) || score === 0) {
                                winston.debug(`Subtask ${subtaskIndex}, case ${index}: zero, skipping the rest.`);
                                skipped = true;
                            }
                            updateCurrentSubtaskScore();
                            await reportProgress();
                        }
                    }
                } else {
                    // Non skippable, run all immediately
                    const caseTasks: Promise<void>[] = [];
                    for (let index = 0; index < currentTask.cases.length; index++) {
                        const currentTaskResult = currentResult.cases[index];
                        if (!validDAG || !validDep) {
                            currentTaskResult.status = TaskStatus.Skipped;
                            currentTaskResult.result.scoringRate = 0;
                            continue;
                        }
                        caseTasks.push((async () => {
                            const currentTaskResult = currentResult.cases[index];
                            winston.verbose(`Judging ${subtaskIndex}, case ${index}.`);
                            try {
                                currentTaskResult.result = await judgeTestcaseWrapper(currentTask.cases[index], async () => {
                                    currentTaskResult.status = TaskStatus.Running;
                                    await reportProgress();
                                });
                                currentTaskResult.status = TaskStatus.Done;
                            } catch (err) {
                                currentTaskResult.status = TaskStatus.Failed;
                                currentTaskResult.errorMessage = err.toString();
                                winston.warn(`Task runner error: ${err.toString()} (subtask ${subtaskIndex}, case ${index})`);
                            }
                            updateCurrentSubtaskScore();
                            await reportProgress();
                        })());
                    }
                    await Promise.all(caseTasks);
                }
                updateCurrentSubtaskScore();
                winston.verbose(`Subtask ${subtaskIndex}, finished`);
            }
            return { subtasks: results };
        }
    }
    protected abstract judgeTestcase(curCase: TestcaseJudge, started: () => Promise<void>): Promise<TestcaseDetails>;

    async cleanup() { }
}
