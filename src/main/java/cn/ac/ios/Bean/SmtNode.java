package cn.ac.ios.Bean;

import com.github.hycos.regex2smtlib.Translator;
import com.github.hycos.regex2smtlib.translator.exception.FormatNotAvailableException;
import com.github.hycos.regex2smtlib.translator.exception.TranslationException;

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

    public String toSmtLib() {
        StringBuilder sb = new StringBuilder();

        // 如果当前正则数组为1，直接生成正则对应的SMT-LIB表达式
        if (intersectionRegexes.size() == 1) {
            try {
                String regexsmt = Translator.INSTANCE.translate("cvc4", intersectionRegexes.get(0));
                // System.out.println(regexsmt);
                sb.append(regexsmt);
            } catch (FormatNotAvailableException | TranslationException e) {
                throw new RuntimeException(e);
            }
        } else {
            // 如果当前正则数组大于1，生成交集表达式
            sb.append("(re.inter ");
            for (String regex : intersectionRegexes) {
                try {
                    String regexsmt = Translator.INSTANCE.translate("cvc4", regex);
                    sb.append(regexsmt).append(" ");
                } catch (FormatNotAvailableException | TranslationException e) {
                    throw new RuntimeException(e);
                }
            }
            sb.append(")");
        }

        if (next != null) {
            sb.append(" ");
            sb.append(next.toSmtLib());
        }

        return sb.toString();
    }
}
