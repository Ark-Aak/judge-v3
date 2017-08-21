import _ = require('lodash');
import winston = require('winston');
import { JudgeResult, OverallResult, TestcaseResultType, TaskStatus, ErrorType, SubtaskResult, TestcaseResult, TestcaseDetails } from './interfaces';

export interface JudgeResultSubmit {
    taskId: number;
    time: number;
    memory: number;
    score: number;
    statusNumber: number;
    statusString: string;
    result: OverallResult;
}

const compileError = "Compile Error",
    systemError = "System Error",
    testdataError = "No Testdata";

export const statusToString = {};
statusToString[TestcaseResultType.Accepted] = "Accepted";
statusToString[TestcaseResultType.WrongAnswer] = "Wrong Answer";
statusToString[TestcaseResultType.PartiallyCorrect] = "Partially Correct";
statusToString[TestcaseResultType.MemoryLimitExceeded] = "Memory Limit Exceeded";
statusToString[TestcaseResultType.TimeLimitExceeded] = "Time Limit Exceeded";
statusToString[TestcaseResultType.OutputLimitExceeded] = "Output Limit Exceeded";
statusToString[TestcaseResultType.RuntimeError] = "Runtime Error";
statusToString[TestcaseResultType.FileError] = "File Error";
statusToString[TestcaseResultType.JudgementFailed] = "Judgement Failed";
statusToString[TestcaseResultType.InvalidInteraction] = "Invalid Interaction";

export function firstNonAC(t: TestcaseResultType[]): TestcaseResultType {
    if (t.every(v => v === TestcaseResultType.Accepted)) {
        return TestcaseResultType.Accepted
    } else {
        return t.find(r => r !== TestcaseResultType.Accepted);
    }
}

export function convertResult(id: number, source: OverallResult): JudgeResultSubmit {
    winston.debug(`Converting result for ${id}`, source);
    let time = NaN,
        memory = NaN,
        score = NaN,
        done = true,
        statusString = null;

    if (source.compile && source.compile.status === TaskStatus.Failed) {
        statusString = compileError;
        score = 0;
    } else if (source.error != null) {
        done = false;
        if (source.error === ErrorType.TestDataError) {
            statusString = testdataError;
        } else {
            statusString = systemError;
        }
    } else if (source.judge != null && source.judge.subtasks != null) {
        const forEveryTestcase = function <TParam>(map: (v: TestcaseDetails) => TParam, reduce: (v: TParam[]) => TParam): TParam {
            return reduce(source.judge.subtasks.map(s => reduce(s.cases.filter(c => c.result != null).map(c => map(c.result)))));
        }
        time = forEveryTestcase(c => c.time, _.sum);
        memory = forEveryTestcase(c => c.memory, _.max);

        if (source.judge.subtasks.some(s => s.cases.some(c => c.status === TaskStatus.Failed))) {
            winston.debug(`Some subtasks failed, returning system error`);
            statusString = systemError;
        } else {
            score = _.sum(source.judge.subtasks.map(s => s.score));
            const finalResult = forEveryTestcase(c => c.type, firstNonAC);
            statusString = statusToString[finalResult];
        }
    } else {
        statusString = systemError;
    }

    const result = {
        taskId: id,
        time: time,
        memory: memory,
        score: score,
        statusNumber: done ? TaskStatus.Done : TaskStatus.Failed,
        statusString: statusString,
        result: source
    };
    winston.debug(`Result for ${id}`, result);
    return result;
}