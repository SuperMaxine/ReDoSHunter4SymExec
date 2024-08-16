package cn.ac.ios.Bean;

import com.github.hycos.regex2smtlib.Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class SmtNode{
    private List<String> intersectionRegexes;
    private SmtNode next;

    public SmtNode(List<String> intersectionRegexes, SmtNode next) {
        this.intersectionRegexes = intersectionRegexes;
        this.next = next;
    }

    public SmtNode(List<String> intersectionRegexes) {
        this.intersectionRegexes = intersectionRegexes;
        this.next = null;
    }

    public SmtNode(SmtNode smtNode) {
        this.intersectionRegexes = new ArrayList<>(smtNode.intersectionRegexes);
        this.next = smtNode.next;
    }

    public List<String> getIntersectionRegexes() {
        return intersectionRegexes;
    }

    public SmtNode appendNode(SmtNode node) {
        if (this.next == null) {
            this.next = node;
        } else {
            SmtNode temp = this.next;
            while (temp.next != null) {
                temp = temp.next;
            }
            temp.next = node;
        }
        return this;
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("SmtNode{");
        sb.append("intersectionRegexes=").append(intersectionRegexes);
        if (next != null) {
            sb.append(", next=").append(next);
        }
        sb.append('}');
        return sb.toString();
    }

    public String toSmtLib() throws TranslationException, FormatNotAvailableException {
        StringBuilder result = new StringBuilder();


        ArrayList<String> smtlibForSingleRegexes = new ArrayList<>();
        for (String regex : intersectionRegexes) {
            String regexsmt = Translator.INSTANCE.translate("cvc4", regex);
            if (regexsmt.equals("")) {
                continue;
            }
            smtlibForSingleRegexes.add(regexsmt);
        }

        if (smtlibForSingleRegexes.isEmpty()) {
            ; //保持result为空
        }
        else if (smtlibForSingleRegexes.size() == 1) {
            result.append(smtlibForSingleRegexes.get(0)); // result为唯一非空正则
        }
        else {
            result.append("(re.inter ");
            for (String regex : smtlibForSingleRegexes) {
                if (!regex.equals("")) {
                    result.append(regex).append(" ");
                }
            }
            result.append(")"); // result为非空正则的交集
        }

        if (next != null) {
            String next = this.next.toSmtLib();
            if (!next.equals("")) {
                if (!result.toString().equals("")) {
                    return "(re.++ " + result.toString() + " " + next + ")";
                } else {
                    return next;
                }
            }
        }

        // 1. 当前节点regex为空，next为空，返回空字符串
        // 2. 当前节点regex为空，next不为空，返回next
        // 3. 当前节点regex不为空，next为空，返回当前节点regex
        // 4. 当前节点regex不为空，next不为空，返回当前节点regex和next的连接
        return result.toString();
    }

    public static String getSMTLIB(String regex) {
        String result = "";
        try {
            // 创建并启动进程
            ProcessBuilder processBuilder = new ProcessBuilder("./IntersectionK");
            processBuilder.redirectErrorStream(true); // 将错误输出和标准输出合并
            Process process = processBuilder.start();

            // 通过进程的输出流向其标准输入写入数据
            BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(process.getOutputStream()));
            writer.write(regex);
            writer.newLine();
            writer.flush();
            writer.close(); // 完成写入后需要关闭流

            // 读取进程的输出
            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                // System.out.println(line);
                result += line;
            }
            reader.close();


            // 等待进程结束
            int exitCode = process.waitFor();
            // System.out.println("Exited with code: " + exitCode);
            // 如果进程错误退出，抛出异常
            if (exitCode != 0) {
                throw new RuntimeException("Process exited with error code " + exitCode);
            }
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
        return result;
    }

}
